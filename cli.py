#!/usr/bin/env python3
"""
Octra CLI Wallet - Refactored v0.1.0

Bu dosya orijinal kodun işlevselliğini koruyarak okunabilirlik,
hata yönetimi ve modülerlik için yeniden düzenlenmiştir.
Kullanım: ~/.octra/wallet.json veya çalıştırma dizininde wallet.json aranır.

Not: Gerçek bir repo'ya koymadan önce gizli anahtarların (wallet.json) güvenliğini
kontrol et. Bu kod, CLI/terminal UI ile çalışmak üzere tasarlanmıştır.
"""

from __future__ import annotations

import asyncio
import base64
import hashlib
import hmac
import json
import os
import re
import secrets
import shutil
import signal
import ssl
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import aiohttp
import nacl.signing
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

# ------------------------
# Config / Constants
# ------------------------
MU = 1_000_000
DEFAULT_RPC = "http://localhost:8080"
WALLET_LOCATIONS = [Path.home() / ".octra" / "wallet.json", Path("wallet.json")]
B58_RE = re.compile(r"^oct[1-9A-HJ-NP-Za-km-z]{44}$")
SPINNER_FRAMES = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"]

# Terminal colors (minimal)
C = {
    "r": "\033[0m",
    "b": "\033[34m",
    "c": "\033[36m",
    "g": "\033[32m",
    "y": "\033[33m",
    "R": "\033[31m",
    "B": "\033[1m",
    "bg": "\033[44m",
    "bgr": "\033[41m",
    "bgg": "\033[42m",
    "w": "\033[37m",
}

# ------------------------
# Utilities (terminal)
# ------------------------
def cls() -> None:
    os.system("cls" if os.name == "nt" else "clear")


def term_size() -> Tuple[int, int]:
    return shutil.get_terminal_size((80, 25))


def at(x: int, y: int, text: str, cl: str = "") -> None:
    """Move cursor and print text (no newline)."""
    print(f"\033[{y};{x}H{cl}{text}{C['r']}", end="")


def input_at(x: int, y: int, prompt: str = "") -> str:
    """Blocking input placed at position (x,y)."""
    print(f"\033[{y};{x}H", end="", flush=True)
    return input(prompt)


# Async wrapper for blocking input
_executor = ThreadPoolExecutor(max_workers=1)


async def ainput_at(x: int, y: int) -> str:
    print(f"\033[{y};{x}H", end="", flush=True)
    loop = asyncio.get_event_loop()
    return await loop.run_in_executor(_executor, input)


# ------------------------
# Wallet and crypto helpers
# ------------------------
@dataclass
class Wallet:
    priv: str
    addr: str
    rpc: str
    signing_key: nacl.signing.SigningKey
    pub_b64: str

    @classmethod
    def load_from_file(cls, paths: List[Path]) -> Optional["Wallet"]:
        """Try to load wallet from a list of candidate paths."""
        for p in paths:
            try:
                if not p.exists():
                    continue
                with p.open("r") as f:
                    d = json.load(f)
                priv = d.get("priv")
                addr = d.get("addr")
                rpc = d.get("rpc", DEFAULT_RPC)
                if not priv or not addr:
                    continue
                sk = nacl.signing.SigningKey(base64.b64decode(priv))
                pub_b64 = base64.b64encode(sk.verify_key.encode()).decode()
                return cls(priv=priv, addr=addr, rpc=rpc, signing_key=sk, pub_b64=pub_b64)
            except Exception:
                continue
        return None


# Encryption key derivation used by client-side balance encryption v2
def derive_encryption_key_v2(priv_b64: str) -> bytes:
    priv_bytes = base64.b64decode(priv_b64)
    salt = b"octra_encrypted_balance_v2"
    return hashlib.sha256(salt + priv_bytes).digest()[:32]


def encrypt_client_balance(balance_raw: int, priv_b64: str) -> str:
    key = derive_encryption_key_v2(priv_b64)
    aes = AESGCM(key)
    nonce = secrets.token_bytes(12)
    plaintext = str(balance_raw).encode()
    ct = aes.encrypt(nonce, plaintext, None)
    return "v2|" + base64.b64encode(nonce + ct).decode()


def decrypt_client_balance(enc: str, priv_b64: str) -> int:
    """Support both old custom XOR v1 and v2 AESGCM format. Return integer raw balance."""
    if not enc or enc == "0":
        return 0
    try:
        if enc.startswith("v2|"):
            raw = base64.b64decode(enc[3:])
            if len(raw) < 13:
                return 0
            nonce = raw[:12]
            ciphertext = raw[12:]
            key = derive_encryption_key_v2(priv_b64)
            aes = AESGCM(key)
            plaintext = aes.decrypt(nonce, ciphertext, None)
            return int(plaintext.decode())
        else:
            # legacy v1 handling (best-effort)
            priv_bytes = base64.b64decode(priv_b64)
            salt = b"octra_encrypted_balance_v1"
            key = hashlib.sha256(salt + priv_bytes).digest() + hashlib.sha256(priv_bytes + salt).digest()
            key = key[:32]
            data = base64.b64decode(enc)
            if len(data) < 32:
                return 0
            nonce = data[:16]
            tag = data[16:32]
            encrypted = data[32:]
            expected_tag = hashlib.sha256(nonce + encrypted + key).digest()[:16]
            if not hmac.compare_digest(tag, expected_tag):
                return 0
            out = bytearray()
            key_hash = hashlib.sha256(key + nonce).digest()
            for i, b in enumerate(encrypted):
                out.append(b ^ key_hash[i % 32])
            return int(out.decode())
    except Exception:
        return 0


def derive_shared_secret_for_claim(my_priv_b64: str, ephemeral_pub_b64: str) -> bytes:
    """Deterministic shared secret derivation used to decrypt private amounts."""
    sk = nacl.signing.SigningKey(base64.b64decode(my_priv_b64))
    my_pub = sk.verify_key.encode()
    eph = base64.b64decode(ephemeral_pub_b64)
    # canonical ordering to avoid ambiguity
    smaller, larger = (eph, my_pub) if eph < my_pub else (my_pub, eph)
    combined = smaller + larger
    r1 = hashlib.sha256(combined).digest()
    r2 = hashlib.sha256(r1 + b"OCTRA_SYMMETRIC_V1").digest()
    return r2[:32]


def decrypt_private_amount(encrypted_data: str, shared_secret: bytes) -> Optional[int]:
    """Decrypt amounts in private transfers (v2 AESGCM expected)."""
    if not encrypted_data or not encrypted_data.startswith("v2|"):
        return None
    try:
        raw = base64.b64decode(encrypted_data[3:])
        if len(raw) < 28:
            return None
        nonce = raw[:12]
        ciphertext = raw[12:]
        aes = AESGCM(shared_secret)
        plaintext = aes.decrypt(nonce, ciphertext, None)
        return int(plaintext.decode())
    except Exception:
        return None


# ------------------------
# RPC Client
# ------------------------
class RPCClient:
    def __init__(self, rpc_base: str, priv: str):
        self.rpc = rpc_base.rstrip("/")
        self.priv = priv
        self._session: Optional[aiohttp.ClientSession] = None
        self._ssl = ssl.create_default_context()

    async def _ensure_session(self) -> aiohttp.ClientSession:
        if self._session and not self._session.closed:
            return self._session
        connector = aiohttp.TCPConnector(ssl=self._ssl, force_close=True)
        self._session = aiohttp.ClientSession(connector=connector, timeout=aiohttp.ClientTimeout(total=10), json_serialize=json.dumps)
        return self._session

    async def close(self) -> None:
        if self._session:
            await self._session.close()

    async def req(self, method: str, path: str, data: Any = None, timeout: int = 10) -> Tuple[int, str, Optional[Any]]:
        """Generic request. Returns (status, text, json_or_none)."""
        await self._ensure_session()
        url = f"{self.rpc}{path}"
        try:
            kwargs = {}
            if method.upper() == "POST" and data is not None:
                kwargs["json"] = data
            async with getattr(self._session, method.lower())(url, **kwargs) as resp:
                text = await resp.text()
                try:
                    j = json.loads(text) if text.strip() else None
                except Exception:
                    j = None
                return resp.status, text, j
        except asyncio.TimeoutError:
            return 0, "timeout", None
        except Exception as e:
            return 0, str(e), None

    async def req_private(self, path: str, method: str = "GET", data: Any = None) -> Tuple[bool, Any]:
        """Requests to private endpoints which require X-Private-Key header."""
        await self._ensure_session()
        headers = {"X-Private-Key": self.priv}
        url = f"{self.rpc}{path}"
        try:
            kwargs = {"headers": headers}
            if method.upper() == "POST" and data is not None:
                kwargs["json"] = data
            async with getattr(self._session, method.lower())(url, **kwargs) as resp:
                text = await resp.text()
                if resp.status == 200:
                    try:
                        return True, json.loads(text) if text.strip() else {}
                    except Exception:
                        return True, {}
                return False, {"error": f"HTTP {resp.status}"}
        except Exception as e:
            return False, {"error": str(e)}


# ------------------------
# High-level wallet operations (async)
# ------------------------
class OctraClient:
    def __init__(self, wallet: Wallet):
        self.wallet = wallet
        self.rpc = RPCClient(wallet.rpc, wallet.priv)
        self.history: List[Dict[str, Any]] = []
        self._last_history_update = 0.0
        self._last_state_update = 0.0
        self.cached_cb: Optional[float] = None
        self.cached_cn: Optional[int] = None
        self._spinner_idx = 0
        self._stop = threading.Event()

    # ------------------------
    # low-level helpers
    # ------------------------
    async def _staging(self) -> Tuple[int, Optional[Any], Optional[Any]]:
        return await self.rpc.req("GET", "/staging")

    async def get_state(self) -> Tuple[Optional[int], Optional[float]]:
        """Get cached or fresh balance & nonce. Returns (nonce, balance)."""
        now = time.time()
        if self.cached_cb is not None and (now - self._last_state_update) < 30:
            return self.cached_cn, self.cached_cb

        s, t, j = await self.rpc.req("GET", f"/balance/{self.wallet.addr}")
        s2, _, j2 = await self._staging()
        if s == 200 and j:
            try:
                cn = int(j.get("nonce", 0))
                cb = float(j.get("balance", 0))
            except Exception:
                cn, cb = None, None
            self.cached_cn, self.cached_cb = cn, cb
            self._last_state_update = now
            # check staged transactions for nonce bumps
            if s2 == 200 and j2:
                our = [tx for tx in j2.get("staged_transactions", []) if tx.get("from") == self.wallet.addr]
                if our:
                    self.cached_cn = max(self.cached_cn or 0, max(int(tx.get("nonce", 0)) for tx in our))
            return self.cached_cn, self.cached_cb
        elif s == 404:
            self.cached_cn, self.cached_cb = 0, 0.0
            self._last_state_update = now
            return 0, 0.0
        elif s == 200 and t and not j:
            # text-based fallback "balance nonce"
            try:
                parts = t.strip().split()
                if len(parts) >= 2:
                    cb = float(parts[0]) if parts[0].replace(".", "").isdigit() else 0.0
                    cn = int(parts[1]) if parts[1].isdigit() else 0
                    self.cached_cn, self.cached_cb = cn, cb
                    self._last_state_update = now
                    return cn, cb
            except Exception:
                pass
        return None, None

    async def get_encrypted_balance(self) -> Optional[Dict[str, Any]]:
        ok, result = await self.rpc.req_private(f"/view_encrypted_balance/{self.wallet.addr}")
        if ok:
            try:
                return {
                    "public": float(result.get("public_balance", "0").split()[0]),
                    "public_raw": int(result.get("public_balance_raw", "0")),
                    "encrypted": float(result.get("encrypted_balance", "0").split()[0]),
                    "encrypted_raw": int(result.get("encrypted_balance_raw", "0")),
                    "total": float(result.get("total_balance", "0").split()[0]),
                }
            except Exception:
                return None
        return None

    async def encrypt_balance(self, amount: float) -> Tuple[bool, Any]:
        enc_data = await self.get_encrypted_balance()
        if not enc_data:
            return False, {"error": "cannot get balance"}
        current_encrypted_raw = enc_data["encrypted_raw"]
        new_encrypted_raw = current_encrypted_raw + int(amount * MU)
        encrypted_value = encrypt_client_balance(new_encrypted_raw, self.wallet.priv)
        data = {
            "address": self.wallet.addr,
            "amount": str(int(amount * MU)),
            "private_key": self.wallet.priv,
            "encrypted_data": encrypted_value,
        }
        s, t, j = await self.rpc.req("POST", "/encrypt_balance", data)
        if s == 200:
            return True, j
        return False, {"error": j.get("error", t) if j else t}

    async def decrypt_balance(self, amount: float) -> Tuple[bool, Any]:
        enc_data = await self.get_encrypted_balance()
        if not enc_data:
            return False, {"error": "cannot get balance"}
        current_encrypted_raw = enc_data["encrypted_raw"]
        if current_encrypted_raw < int(amount * MU):
            return False, {"error": "insufficient encrypted balance"}
        new_encrypted_raw = current_encrypted_raw - int(amount * MU)
        encrypted_value = encrypt_client_balance(new_encrypted_raw, self.wallet.priv)
        data = {
            "address": self.wallet.addr,
            "amount": str(int(amount * MU)),
            "private_key": self.wallet.priv,
            "encrypted_data": encrypted_value,
        }
        s, t, j = await self.rpc.req("POST", "/decrypt_balance", data)
        if s == 200:
            return True, j
        return False, {"error": j.get("error", t) if j else t}

    async def get_address_info(self, address: str) -> Optional[Dict[str, Any]]:
        s, t, j = await self.rpc.req("GET", f"/address/{address}")
        if s == 200:
            return j
        return None

    async def get_public_key(self, address: str) -> Optional[str]:
        s, t, j = await self.rpc.req("GET", f"/public_key/{address}")
        if s == 200 and isinstance(j, dict):
            return j.get("public_key")
        return None

    async def create_private_transfer(self, to_addr: str, amount: float) -> Tuple[bool, Any]:
        addr_info = await self.get_address_info(to_addr)
        if not addr_info or not addr_info.get("has_public_key"):
            return False, {"error": "Recipient has no public key"}
        to_public_key = await self.get_public_key(to_addr)
        if not to_public_key:
            return False, {"error": "Cannot get recipient public key"}
        data = {
            "from": self.wallet.addr,
            "to": to_addr,
            "amount": str(int(amount * MU)),
            "from_private_key": self.wallet.priv,
            "to_public_key": to_public_key,
        }
        s, t, j = await self.rpc.req("POST", "/private_transfer", data)
        if s == 200:
            return True, j
        return False, {"error": j.get("error", t) if j else t}

    async def get_pending_transfers(self) -> List[Dict[str, Any]]:
        ok, result = await self.rpc.req_private(f"/pending_private_transfers?address={self.wallet.addr}")
        if ok:
            return result.get("pending_transfers", [])
        return []

    async def claim_private_transfer(self, transfer_id: Any) -> Tuple[bool, Any]:
        data = {"recipient_address": self.wallet.addr, "private_key": self.wallet.priv, "transfer_id": transfer_id}
        s, t, j = await self.rpc.req("POST", "/claim_private_transfer", data)
        if s == 200:
            return True, j
        return False, {"error": j.get("error", t) if j else t}

    # ------------------------
    # Transactions (mk / snd)
    # ------------------------
    def _make_tx(self, to: str, amount: float, nonce: int, msg: Optional[str] = None) -> Tuple[Dict[str, Any], str]:
        """Create transaction dict and its blake-like hash."""
        tx = {
            "from": self.wallet.addr,
            "to_": to,
            "amount": str(int(amount * MU)),
            "nonce": int(nonce),
            "ou": "1" if amount < 1000 else "3",
            "timestamp": time.time(),
        }
        if msg:
            tx["message"] = msg
        bl = json.dumps({k: v for k, v in tx.items() if k != "message"}, separators=(",", ":"))
        sig = base64.b64encode(self.wallet.signing_key.sign(bl.encode()).signature).decode()
        tx.update(signature=sig, public_key=self.wallet.pub_b64)
        return tx, hashlib.sha256(bl.encode()).hexdigest()

    async def send_tx(self, tx: Dict[str, Any]) -> Tuple[bool, Any, float, Optional[Any]]:
        t0 = time.time()
        s, t, j = await self.rpc.req("POST", "/send-tx", tx)
        dt = time.time() - t0
        if s == 200:
            if j and j.get("status") == "accepted":
                return True, j.get("tx_hash", ""), dt, j
            elif isinstance(t, str) and t.lower().startswith("ok"):
                return True, t.split()[-1], dt, None
        return False, json.dumps(j) if j else t, dt, j

    # ------------------------
    # History & explorer (best-effort)
    # ------------------------
    async def update_history(self) -> None:
        now = time.time()
        if now - self._last_history_update < 60 and self.history:
            return
        s, t, j = await self.rpc.req("GET", f"/address/{self.wallet.addr}?limit=20")
        if s != 200 or (not j and not t):
            return
        if j and "recent_transactions" in j:
            tx_hashes = [ref["hash"] for ref in j.get("recent_transactions", [])]
            tx_results = await asyncio.gather(*[self.rpc.req("GET", f"/tx/{hsh}", None, 5) for hsh in tx_hashes], return_exceptions=True)
            existing = {tx["hash"] for tx in self.history}
            new_hist = []
            for ref, res in zip(j.get("recent_transactions", []), tx_results):
                if isinstance(res, Exception):
                    continue
                s2, _, j2 = res
                if s2 == 200 and j2 and "parsed_tx" in j2:
                    p = j2["parsed_tx"]
                    tx_hash = ref["hash"]
                    if tx_hash in existing:
                        continue
                    incoming = p.get("to") == self.wallet.addr
                    ar = p.get("amount_raw", p.get("amount", "0"))
                    amt = float(ar) if "." in str(ar) else int(ar) / MU
                    msg = None
                    if "data" in j2:
                        try:
                            data = json.loads(j2["data"])
                            msg = data.get("message")
                        except Exception:
                            pass
                    new_hist.append({
                        "time": datetime.fromtimestamp(p.get("timestamp", 0)),
                        "hash": tx_hash,
                        "amt": amt,
                        "to": p.get("to") if not incoming else p.get("from"),
                        "type": "in" if incoming else "out",
                        "ok": True,
                        "nonce": p.get("nonce", 0),
                        "epoch": ref.get("epoch", 0),
                        "msg": msg,
                    })
            one_hour_ago = datetime.now() - timedelta(hours=1)
            self.history[:] = sorted(new_hist + [tx for tx in self.history if tx.get("time", datetime.now()) > one_hour_ago], key=lambda x: x["time"], reverse=True)[:50]
            self._last_history_update = now
        elif s == 404 or (s == 200 and t and "no transactions" in t.lower()):
            self.history.clear()
            self._last_history_update = now

    # ------------------------
    # Clean shutdown
    # ------------------------
    async def close(self) -> None:
        await self.rpc.close()


# ------------------------
# UI / Interaction (kept intentionally similar to original)
# ------------------------
async def spin_animation(client: OctraClient, x: int, y: int, msg: str):
    try:
        while True:
            frame = SPINNER_FRAMES[client._spinner_idx % len(SPINNER_FRAMES)]
            at(x, y, f"{C['c']}{frame} {msg}", C["r"])
            client._spinner_idx += 1
            await asyncio.sleep(0.1)
    except asyncio.CancelledError:
        at(x, y, " " * (len(msg) + 3), "")


def draw_box(x: int, y: int, w: int, h: int, title: str = "") -> None:
    print(f"\033[{y};{x}H{C['bg']}{C['w']}┌{'─' * (w - 2)}┐{C['r']}")
    if title:
        print(f"\033[{y};{x}H{C['bg']}{C['w']}┤ {C['B']}{title} {C['w']}├{C['r']}")
    for i in range(1, h - 1):
        print(f"\033[{y + i};{x}H{C['bg']}{C['w']}│{' ' * (w - 2)}│{C['r']}")
    print(f"\033[{y + h - 1};{x}H{C['bg']}{C['w']}└{'─' * (w - 2)}┘{C['r']}")


async def main_loop(client: OctraClient):
    """Main interactive loop. Kept simple and similar to original menu layout."""
    stop_flag = threading.Event()

    def handle_sig(signum, frame):
        stop_flag.set()

    signal.signal(signal.SIGINT, handle_sig)
    signal.signal(signal.SIGTERM, handle_sig)

    while not stop_flag.is_set():
        try:
            # draw main screen
            cls()
            cr_w, cr_h = term_size()
            header = f" octra client v0.1.0 (private) │ {datetime.now().strftime('%H:%M:%S')} "
            at((cr_w - len(header)) // 2, 1, header, C["B"] + C["w"])
            sidebar_w = 28
            draw_box(2, 3, sidebar_w, 15, "commands")
            at(4, 5, "[1] send tx", C["w"])
            at(4, 6, "[2] refresh", C["w"])
            at(4, 7, "[3] multi send", C["w"])
            at(4, 8, "[4] encrypt balance", C["w"])
            at(4, 9, "[5] decrypt balance", C["w"])
            at(4, 10, "[6] private transfer", C["w"])
            at(4, 11, "[7] claim transfers", C["w"])
            at(4, 12, "[8] export keys", C["w"])
            at(4, 13, "[9] clear hist", C["w"])
            at(4, 14, "[0] exit", C["w"])
            # explorer
            explorer_x = sidebar_w + 4
            explorer_w = cr_w - explorer_x - 2
            await client.update_history()
            n, b = await client.get_state()
            draw_box(explorer_x, 3, explorer_w, cr_h - 6, "wallet explorer")
            at(explorer_x + 2, 5, "address:", C["c"])
            at(explorer_x + 12, 5, client.wallet.addr, C["w"])
            at(explorer_x + 2, 6, "balance:", C["c"])
            at(explorer_x + 12, 6, f"{b:.6f} oct" if b is not None else "---", C["g"] if b else C["w"])
            at(explorer_x + 2, 7, "nonce:  ", C["c"])
            at(explorer_x + 12, 7, str(n) if n is not None else "---", C["w"])
            at(explorer_x + 2, 8, "public: ", C["c"])
            at(explorer_x + 12, 8, client.wallet.pub_b64[:40] + "...", C["w"])
            # recent txs header
            at(explorer_x + 2, 10, "recent transactions:", C["B"] + C["c"])
            if not client.history:
                at(explorer_x + 2, 12, "no transactions yet", C["y"])
            else:
                at(explorer_x + 2, 12, "time     type  amount      address", C["c"])
                at(explorer_x + 2, 13, "─" * (explorer_w - 4), C["w"])
                display_count = 0
                for tx in client.history[:min(len(client.history), cr_h - 18)]:
                    y_pos = 14 + display_count
                    at(explorer_x + 2, y_pos, tx["time"].strftime("%H:%M:%S"), C["y"] if not tx.get("epoch") else C["w"])
                    at(explorer_x + 11, y_pos, " in" if tx["type"] == "in" else "out", C["g"] if tx["type"] == "in" else C["R"])
                    at(explorer_x + 16, y_pos, f"{float(tx['amt']):>10.6f}", C["w"])
                    at(explorer_x + 28, y_pos, str(tx.get("to", "---")), C["y"])
                    status_text = "pen" if not tx.get("epoch") else f"e{tx.get('epoch', 0)}"
                    at(explorer_x + explorer_w - 6, y_pos, status_text, C["y"] + C["B"] if not tx.get("epoch") else C["c"])
                    display_count += 1

            # read command
            at(2, cr_h - 2, "command: ", C["B"] + C["y"])
            cmd = await ainput_at(12, cr_h - 2)
            cmd = (cmd or "").strip()
            # dispatch basic commands only to keep this refactor concise
            if cmd == "1":
                await send_tx_flow(client)
            elif cmd == "2":
                client.cached_cn = client.cached_cb = None
                await client.get_state()
                await client.update_history()
            elif cmd == "3":
                await multi_send_flow(client)
            elif cmd == "4":
                await encrypt_balance_flow(client)
            elif cmd == "5":
                await decrypt_balance_flow(client)
            elif cmd == "6":
                await private_transfer_flow(client)
            elif cmd == "7":
                await claim_transfers_flow(client)
            elif cmd == "8":
                export_wallet_flow(client.wallet)
            elif cmd == "9":
                client.history.clear()
            elif cmd in ["0", "q", ""]:
                break
        except Exception:
            # Prevent crash on UI error; continue loop
            await asyncio.sleep(0.1)
            continue
    await client.close()


# ------------------------
# UI flows (simplified, similar behaviour to original)
# ------------------------
async def send_tx_flow(client: OctraClient):
    cls()
    cr_w, cr_h = term_size()
    w, hb = 85, 26
    x = max(2, (cr_w - w) // 2)
    y = max(2, (cr_h - hb) // 2)
    draw_box(x, y, w, hb, "send transaction")
    at(x + 2, y + 2, "to address: (or [esc] to cancel)", C["y"])
    to = (await ainput_at(x + 2, y + 4)).strip()
    if not to or to.lower() == "esc":
        return
    if not B58_RE.match(to):
        at(x + 2, y + 14, "invalid address!", C["bgr"] + C["w"])
        await ainput_at(x + 2, y + 16)
        return
    at(x + 2, y + 7, "amount: (or [esc] to cancel)", C["y"])
    a_in = (await ainput_at(x + 2, y + 9)).strip()
    if not a_in or a_in.lower() == "esc":
        return
    if not re.match(r"^\d+(\.\d+)?$", a_in) or float(a_in) <= 0:
        at(x + 2, y + 14, "invalid amount!", C["bgr"] + C["w"])
        await ainput_at(x + 2, y + 16)
        return
    amount = float(a_in)
    at(x + 2, y + 12, "message (optional, enter to skip):", C["y"])
    msg = (await ainput_at(x + 2, y + 14)).strip()
    if not msg:
        msg = None
    # refresh state
    client.cached_cn = client.cached_cb = None
    n, b = await client.get_state()
    if n is None:
        at(x + 2, y + 17, "failed to get nonce!", C["bgr"] + C["w"])
        await ainput_at(x + 2, y + 19)
        return
    if b is None or b < amount:
        at(x + 2, y + 17, f"insufficient balance ({b} < {amount})", C["bgr"] + C["w"])
        await ainput_at(x + 2, y + 19)
        return
    at(x + 2, y + 16, f"send {amount:.6f} oct to {to}? [y/n]:", C["B"] + C["y"])
    confirm = (await ainput_at(x + 45, y + 16)).strip().lower()
    if confirm != "y":
        return
    spin = asyncio.create_task(spin_animation(client, x + 2, y + 22, "sending transaction"))
    tx_obj, _ = client._make_tx(to, amount, (n or 0) + 1, msg)
    ok, hs, dt, r = await client.send_tx(tx_obj)
    spin.cancel()
    try:
        await spin
    except asyncio.CancelledError:
        pass
    if ok:
        at(x + 2, y + 20, "✓ transaction accepted!", C["bgg"] + C["w"])
        at(x + 2, y + 21, f"hash: {hs}", C["g"])
        client.history.insert(0, {"time": datetime.now(), "hash": hs, "amt": amount, "to": to, "type": "out", "ok": True, "msg": msg})
        client.cached_cn = client.cached_cb = None
    else:
        at(x + 2, y + 20, f"✗ transaction failed: {str(hs)[:60]}", C["bgr"] + C["w"])
    await ainput_at(x + 2, y + 23)


async def multi_send_flow(client: OctraClient):
    cls()
    cr_w, cr_h = term_size()
    w, hb = 70, cr_h - 4
    x = max(2, (cr_w - w) // 2)
    y = 2
    draw_box(x, y, w, hb, "multi send")
    at(x + 2, y + 2, "enter recipients (address amount), empty line to finish:", C["y"])
    at(x + 2, y + 3, "type [esc] to cancel", C["c"])
    rcp: List[Tuple[str, float]] = []
    tot = 0.0
    ly = y + 5
    while ly < y + hb - 8:
        at(x + 2, ly, f"[{len(rcp) + 1}] ", C["c"])
        l = (await ainput_at(x + 7, ly)).strip()
        if not l:
            break
        if l.lower() == "esc":
            return
        p = l.split()
        if len(p) == 2 and B58_RE.match(p[0]) and re.match(r"^\d+(\.\d+)?$", p[1]) and float(p[1]) > 0:
            a = float(p[1])
            rcp.append((p[0], a))
            tot += a
            at(x + 50, ly, f"+{a:.6f}", C["g"])
            ly += 1
        else:
            at(x + 50, ly, "invalid!", C["R"])
    if not rcp:
        return
    client.cached_cn = client.cached_cb = None
    n, b = await client.get_state()
    if n is None:
        at(x + 2, y + hb - 5, "failed to get nonce!", C["bgr"] + C["w"])
        await ainput_at(x + 2, y + hb - 3)
        return
    if b is None or b < tot:
        at(x + 2, y + hb - 5, f"insufficient balance! ({b} < {tot})", C["bgr"] + C["w"])
        await ainput_at(x + 2, y + hb - 3)
        return
    at(x + 2, y + hb - 5, f"send all? [y/n] (starting nonce: {n + 1}): ", C["y"])
    if (await ainput_at(x + 48, y + hb - 5)).strip().lower() != "y":
        return
    spin = asyncio.create_task(spin_animation(client, x + 2, y + hb - 3, "sending transactions"))
    batch_size = 5
    batches = [rcp[i : i + batch_size] for i in range(0, len(rcp), batch_size)]
    s_total = f_total = 0
    for batch_idx, batch in enumerate(batches):
        tasks = []
        for i, (to, a) in enumerate(batch):
            idx = batch_idx * batch_size + i
            tx, _ = client._make_tx(to, a, (n or 0) + 1 + idx)
            tasks.append(client.send_tx(tx))
        results = await asyncio.gather(*tasks, return_exceptions=True)
        for res in results:
            if isinstance(res, Exception):
                f_total += 1
            else:
                ok, _, _, _ = res
                if ok:
                    s_total += 1
                else:
                    f_total += 1
    spin.cancel()
    try:
        await spin
    except asyncio.CancelledError:
        pass
    client.cached_cn = client.cached_cb = None
    at(x + 2, y + hb - 2, f"completed: {s_total} success, {f_total} failed", C["bgg"] + C["w"] if f_total == 0 else C["bgr"] + C["w"])
    await ainput_at(x + 2, y + hb - 1)


async def encrypt_balance_flow(client: OctraClient):
    cls()
    cr_w, cr_h = term_size()
    w, hb = 70, 20
    x = max(2, (cr_w - w) // 2)
    y = max(2, (cr_h - hb) // 2)
    draw_box(x, y, w, hb, "encrypt balance")
    n, pub_bal = await client.get_state()
    enc_data = await client.get_encrypted_balance()
    if not enc_data:
        at(x + 2, y + 10, "cannot get encrypted balance info", C["R"])
        await ainput_at(x + 2, y + 12)
        return
    at(x + 2, y + 2, "public balance:", C["c"])
    at(x + 20, y + 2, f"{pub_bal:.6f} oct", C["w"])
    at(x + 2, y + 3, "encrypted:", C["c"])
    at(x + 20, y + 3, f"{enc_data['encrypted']:.6f} oct", C["y"])
    at(x + 2, y + 4, "total:", C["c"])
    at(x + 20, y + 4, f"{enc_data['total']:.6f} oct", C["g"])
    max_encrypt = enc_data["public_raw"] / MU - 1.0
    if max_encrypt <= 0:
        at(x + 2, y + 8, "insufficient public balance (need > 1 oct for fees)", C["R"])
        await ainput_at(x + 2, y + 10)
        return
    at(x + 2, y + 7, f"max encryptable: {max_encrypt:.6f} oct", C["y"])
    at(x + 2, y + 9, "amount to encrypt:", C["y"])
    amount_str = (await ainput_at(x + 21, y + 9)).strip()
    if not amount_str or not re.match(r"^\d+(\.\d+)?$", amount_str) or float(amount_str) <= 0:
        return
    amount = float(amount_str)
    if amount > max_encrypt:
        at(x + 2, y + 11, f"amount too large (max: {max_encrypt:.6f})", C["R"])
        await ainput_at(x + 2, y + 13)
        return
    at(x + 2, y + 11, f"encrypt {amount:.6f} oct? [y/n]:", C["B"] + C["y"])
    if (await ainput_at(x + 30, y + 11)).strip().lower() != "y":
        return
    spin = asyncio.create_task(spin_animation(client, x + 2, y + 14, "encrypting balance"))
    ok, res = await client.encrypt_balance(amount)
    spin.cancel()
    try:
        await spin
    except asyncio.CancelledError:
        pass
    if ok:
        at(x + 2, y + 14, "✓ encryption submitted!", C["bgg"] + C["w"])
        at(x + 2, y + 15, f"tx hash: {res.get('tx_hash', 'unknown')}", C["g"])
    else:
        at(x + 2, y + 14, f"✗ error: {res.get('error', 'unknown')}", C["bgr"] + C["w"])
    await ainput_at(x + 2, y + 17)


async def decrypt_balance_flow(client: OctraClient):
    cls()
    cr_w, cr_h = term_size()
    w, hb = 70, 20
    x = max(2, (cr_w - w) // 2)
    y = max(2, (cr_h - hb) // 2)
    draw_box(x, y, w, hb, "decrypt balance")
    n, pub_bal = await client.get_state()
    enc_data = await client.get_encrypted_balance()
    if not enc_data:
        at(x + 2, y + 10, "cannot get encrypted balance info", C["R"])
        await ainput_at(x + 2, y + 12)
        return
    if enc_data["encrypted_raw"] == 0:
        at(x + 2, y + 8, "no encrypted balance to decrypt", C["R"])
        await ainput_at(x + 2, y + 10)
        return
    max_decrypt = enc_data["encrypted_raw"] / MU
    at(x + 2, y + 7, f"max decryptable: {max_decrypt:.6f} oct", C["y"])
    at(x + 2, y + 9, "amount to decrypt:", C["y"])
    amount_str = (await ainput_at(x + 21, y + 9)).strip()
    if not amount_str or not re.match(r"^\d+(\.\d+)?$", amount_str) or float(amount_str) <= 0:
        return
    amount = float(amount_str)
    if amount > max_decrypt:
        at(x + 2, y + 11, f"amount too large (max: {max_decrypt:.6f})", C["R"])
        await ainput_at(x + 2, y + 13)
        return
    at(x + 2, y + 11, f"decrypt {amount:.6f} oct? [y/n]:", C["B"] + C["y"])
    if (await ainput_at(x + 30, y + 11)).strip().lower() != "y":
        return
    spin = asyncio.create_task(spin_animation(client, x + 2, y + 14, "decrypting balance"))
    ok, res = await client.decrypt_balance(amount)
    spin.cancel()
    try:
        await spin
    except asyncio.CancelledError:
        pass
    if ok:
        at(x + 2, y + 14, "✓ decryption submitted!", C["bgg"] + C["w"])
        at(x + 2, y + 15, f"tx hash: {res.get('tx_hash', 'unknown')}", C["g"])
    else:
        at(x + 2, y + 14, f"✗ error: {res.get('error', 'unknown')}", C["bgr"] + C["w"])
    await ainput_at(x + 2, y + 17)


async def private_transfer_flow(client: OctraClient):
    cls()
    cr_w, cr_h = term_size()
    w, hb = 80, 25
    x = max(2, (cr_w - w) // 2)
    y = max(2, (cr_h - hb) // 2)
    draw_box(x, y, w, hb, "private transfer")
    enc_data = await client.get_encrypted_balance()
    if not enc_data or enc_data["encrypted_raw"] == 0:
        at(x + 2, y + 10, "no encrypted balance available", C["R"])
        await ainput_at(x + 2, y + 12)
        return
    at(x + 2, y + 2, f"encrypted balance: {enc_data['encrypted']:.6f} oct", C["g"])
    at(x + 2, y + 5, "recipient address:", C["y"])
    to_addr = (await ainput_at(x + 2, y + 6)).strip()
    if not to_addr or not B58_RE.match(to_addr):
        at(x + 2, y + 12, "invalid address", C["R"])
        await ainput_at(x + 2, y + 14)
        return
    if to_addr == client.wallet.addr:
        at(x + 2, y + 12, "cannot send to yourself", C["R"])
        await ainput_at(x + 2, y + 14)
        return
    spin = asyncio.create_task(spin_animation(client, x + 2, y + 8, "checking recipient"))
    addr_info = await client.get_address_info(to_addr)
    spin.cancel()
    try:
        await spin
    except asyncio.CancelledError:
        pass
    if not addr_info:
        at(x + 2, y + 12, "recipient address not found on blockchain", C["R"])
        await ainput_at(x + 2, y + 14)
        return
    if not addr_info.get("has_public_key"):
        at(x + 2, y + 12, "recipient has no public key", C["R"])
        at(x + 2, y + 13, "they need to make a transaction first", C["y"])
        await ainput_at(x + 2, y + 15)
        return
    at(x + 2, y + 10, "amount:", C["y"])
    amount_str = (await ainput_at(x + 10, y + 10)).strip()
    if not amount_str or not re.match(r"^\d+(\.\d+)?$", amount_str) or float(amount_str) <= 0:
        return
    amount = float(amount_str)
    if amount > enc_data["encrypted"]:
        at(x + 2, y + 14, f"insufficient encrypted balance", C["R"])
        await ainput_at(x + 2, y + 16)
        return
    at(x + 2, y + 13, f"send {amount:.6f} oct privately to", C["B"])
    at(x + 2, y + 14, to_addr, C["y"])
    at(x + 2, y + 16, "[y]es / [n]o:", C["B"] + C["y"])
    if (await ainput_at(x + 15, y + 16)).strip().lower() != "y":
        return
    spin = asyncio.create_task(spin_animation(client, x + 2, y + 18, "creating private transfer"))
    ok, res = await client.create_private_transfer(to_addr, amount)
    spin.cancel()
    try:
        await spin
    except asyncio.CancelledError:
        pass
    if ok:
        at(x + 2, y + 18, "✓ private transfer submitted!", C["bgg"] + C["w"])
        at(x + 2, y + 19, f"tx hash: {res.get('tx_hash', 'unknown')}", C["g"])
        at(x + 2, y + 20, f"ephemeral key: {res.get('ephemeral_key', 'unknown')[:40]}...", C["c"])
    else:
        at(x + 2, y + 18, f"✗ error: {res.get('error', 'unknown')}", C["bgr"] + C["w"])
    await ainput_at(x + 2, y + 22)


async def claim_transfers_flow(client: OctraClient):
    cls()
    cr_w, cr_h = term_size()
    w, hb = 85, cr_h - 4
    x = max(2, (cr_w - w) // 2)
    y = 2
    draw_box(x, y, w, hb, "claim private transfers")
    spin = asyncio.create_task(spin_animation(client, x + 2, y + 2, "loading pending transfers"))
    transfers = await client.get_pending_transfers()
    spin.cancel()
    try:
        await spin
    except asyncio.CancelledError:
        pass
    if not transfers:
        at(x + 2, y + 10, "no pending transfers", C["y"])
        await ainput_at(x + 2, y + 12)
        return
    at(x + 2, y + 2, f"found {len(transfers)} claimable transfers:", C["B"] + C["g"])
    at(x + 2, y + 4, "#   FROM                AMOUNT         EPOCH   ID", C["c"])
    at(x + 2, y + 5, "─" * (w - 4), C["w"])
    display_y = y + 6
    max_display = min(len(transfers), hb - 12)
    for i, t in enumerate(transfers[:max_display]):
        amount_str = "[encrypted]"
        amount_color = C["y"]
        if t.get("encrypted_data") and t.get("ephemeral_key"):
            try:
                shared = derive_shared_secret_for_claim(client.wallet.priv, t["ephemeral_key"])
                amt = decrypt_private_amount(t["encrypted_data"], shared)
                if amt:
                    amount_str = f"{amt / MU:.6f} OCT"
                    amount_color = C["g"]
            except Exception:
                pass
        at(x + 2, display_y + i, f"[{i+1}]", C["c"])
        at(x + 8, display_y + i, t["sender"][:20] + "...", C["w"])
        at(x + 32, display_y + i, amount_str, amount_color)
        at(x + 48, display_y + i, f"ep{t.get('epoch_id', '?')}", C["c"])
        at(x + 58, display_y + i, f"#{t.get('id', '?')}", C["y"])
    if len(transfers) > max_display:
        at(x + 2, display_y + max_display + 1, f"... and {len(transfers) - max_display} more", C["y"])
    at(x + 2, y + hb - 5, "enter number to claim (0 to cancel):", C["y"])
    choice = (await ainput_at(x + 40, y + hb - 5)).strip()
    if not choice or choice == "0":
        return
    try:
        idx = int(choice) - 1
        if 0 <= idx < len(transfers):
            transfer = transfers[idx]
            transfer_id = transfer["id"]
            spin = asyncio.create_task(spin_animation(client, x + 2, y + hb - 3, f"claiming transfer #{transfer_id}"))
            ok, res = await client.claim_private_transfer(transfer_id)
            spin.cancel()
            try:
                await spin
            except asyncio.CancelledError:
                pass
            if ok:
                at(x + 2, y + hb - 3, f"✓ claimed {res.get('amount', 'unknown')}!", C["bgg"] + C["w"])
            else:
                at(x + 2, y + hb - 3, f"✗ error: {res.get('error', 'unknown')}", C["bgr"] + C["w"])
        else:
            at(x + 2, y + hb - 3, "invalid selection", C["R"])
    except ValueError:
        at(x + 2, y + hb - 3, "invalid number", C["R"])
    await ainput_at(x + 2, y + hb - 1)


def export_wallet_flow(wallet: Wallet):
    cls()
    cr_w, cr_h = term_size()
    w, hb = 70, 15
    x = max(2, (cr_w - w) // 2)
    y = max(2, (cr_h - hb) // 2)
    draw_box(x, y, w, hb, "export keys")
    at(x + 2, y + 2, "current wallet info:", C["c"])
    at(x + 2, y + 4, "address:", C["c"])
    at(x + 11, y + 4, wallet.addr[:32] + "...", C["w"])
    # don't show full private key casually
    at(x + 2, y + 7, "[1] show private key (unsafe!)", C["w"])
    at(x + 2, y + 8, "[2] save full wallet to file", C["w"])
    at(x + 2, y + 9, "[3] copy address to clipboard (if available)", C["w"])
    at(x + 2, y + 11, "[0] cancel", C["w"])
    choice = input_at(x + 10, y + 13).strip()
    if choice == "1":
        at(x + 2, y + 7, "private key (keep secret!):", C["R"])
        # show only partial key to discourage accidental leak
        at(x + 2, y + 8, wallet.priv[:32] + "..." + wallet.priv[-8:], C["R"])
        input_at(x + 2, y + 10)
    elif choice == "2":
        fn = f"octra_wallet_{int(time.time())}.json"
        wallet_data = {"priv": wallet.priv, "addr": wallet.addr, "rpc": wallet.rpc}
        old_umask = os.umask(0o077)
        try:
            with open(fn, "w") as f:
                json.dump(wallet_data, f, indent=2)
            os.chmod(fn, 0o600)
            at(x + 2, y + 9, f"saved to {fn}", C["g"])
            at(x + 2, y + 11, "file contains private key - keep safe!", C["R"])
        except Exception:
            at(x + 2, y + 9, "failed to save file", C["R"])
        finally:
            os.umask(old_umask)
        input_at(x + 2, y + 13)
    elif choice == "3":
        try:
            import pyperclip
            pyperclip.copy(wallet.addr)
            at(x + 2, y + 9, "address copied to clipboard!", C["g"])
        except Exception:
            at(x + 2, y + 9, "clipboard not available", C["R"])
        input_at(x + 2, y + 11)
    else:
        return


# ------------------------
# Entrypoint
# ------------------------
async def run() -> None:
    wallet = Wallet.load_from_file(WALLET_LOCATIONS)
    if not wallet:
        print("[!] wallet.json error or missing. Place wallet.json in ~/.octra/ or current directory.")
        sys.exit(1)
    if not wallet.rpc.startswith("https://") and "localhost" not in wallet.rpc:
        print(f"{C['R']}⚠️  WARNING: Using insecure HTTP connection!{C['r']}")
        time.sleep(2)
    client = OctraClient(wallet)
    try:
        # prefetch state & history
        await client.get_state()
        await client.update_history()
        await main_loop(client)
    finally:
        await client.close()
        _executor.shutdown(wait=False)


if __name__ == "__main__":
    try:
        asyncio.run(run())
    except KeyboardInterrupt:
        pass
    finally:
        cls()
        print(C["r"])
        os._exit(0)
