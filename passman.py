#!/usr/bin/env python3
"""
=====================================================================
 PASSMAN SEJI v2.0 — offline, privacy focus, encrypted password manager
=====================================================================

Usage
    python passman.py [vault_path]        (default: ~/.seji_vault.json)

Dependencies
    pip install cryptography              (pyperclip optional — clipboard)

Security design
    * AES-256-GCM authenticated encryption (nonce + AAD bound to format)
    * Master key: Argon2id (time=3, lanes=4, 64 MiB) if available,
      otherwise PBKDF2-HMAC-SHA256 with 600,000 iterations
    * Unique 16-byte salt, 12-byte nonce per save
    * Atomic save (temp file + fsync + os.replace) with .bak backup
    * Vault file restricted to 0600 on POSIX
    * Auto-lock after inactivity; failed unlocks back off exponentially

Honest limits
    * CPython cannot reliably zero strings from memory; keys are stored
      in bytearrays and cleared best-effort.
    * Anything displayed or copied can be observed on screen/clipboard.
    * Overall security rests on a strong, unique master password.
"""

from __future__ import annotations

import argparse
import base64
import ctypes
import getpass
import hashlib
import hmac
import json
import math
import os
import re
import secrets
import shutil
import stat
import string
import subprocess
import sys
import tempfile
import threading
import time
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional, Tuple

# ---------------------------------------------------------------------
# Dependencies
# ---------------------------------------------------------------------
try:
    from cryptography.exceptions import InvalidTag
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC

    try:  # Argon2id is available in cryptography >= 43
        from cryptography.hazmat.primitives.kdf.argon2 import Argon2id
        HAVE_ARGON2 = True
    except ImportError:
        HAVE_ARGON2 = False
except ImportError:
    sys.exit("Missing dependency. Install it with:  pip install cryptography")

try:
    import pyperclip  # optional clipboard helper
    HAVE_PYPERCLIP = True
except ImportError:
    HAVE_PYPERCLIP = False

# ---------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------
APP_NAME = "PassMan Seji"
VERSION = "2.0.0"
VAULT_VERSION = 2
DEFAULT_VAULT = os.path.join(os.path.expanduser("~"), ".seji_vault.json")
AAD = b"seji-vault-v2"

PBKDF2_ITERATIONS = 600_000
ARGON2_PARAMS: Dict[str, int] = {"iterations": 3, "lanes": 4, "memory_cost": 65_536}

MIN_MASTER_LEN = 12
MIN_GEN_LEN = 8
MAX_ENTRY_LEN = 2048
DEFAULT_AUTOLOCK = 300          # seconds
CLIPBOARD_CLEAR_SECONDS = 30
PASSWORD_AGE_WARN_DAYS = 90
MAX_UNLOCK_ATTEMPTS = 8

_CTRL_RE = re.compile(r"[\x00-\x1f\x7f]")
_URL_OK = re.compile(r"^[A-Za-z0-9._~:/?#\[\]@!$&'()*+,;=%-]*$")

# Small built-in blocklist (illustrative — extend as desired)
COMMON_PASSWORDS = frozenset({
    "password", "password1", "password123", "passw0rd", "123456", "123456789",
    "12345678", "qwerty", "qwerty123", "abc123", "letmein", "admin", "admin123",
    "welcome", "welcome1", "monkey", "iloveyou", "dragon", "football",
    "baseball", "princess", "sunshine", "master", "shadow", "superman",
    "trustno1", "starwars", "whatever", "hello123", "1q2w3e4r", "zaq12wsx",
    "111111", "000000", "access", "mustang", "michael", "jennifer", "flower",
    "hotdog", "pizza", "sunset", "orange", "chocolate", "cookie", "lovely",
})

# 256-word list for passphrases (8 bits per word). Deduplicated at load.
_WORDLIST_RAW = """
amber anchor apple arrow atlas aurora autumn badge bamboo basil beacon beetle birch bison blade bloom
blossom bluff bolt bonus boulder bramble brick brook brush cabin cactus camel candle canyon carbon cedar
cello chalk cherry chorus cinder citrus clover cobalt comet copper coral cosmic cotton coyote crane crater
cricket crimson crystal cypress dahlia dawn delta denim desert diesel dolphin domino drift eagle ember emerald
fable fabric falcon fennel fern fiber fiddle finch fjord flint flora flute forest fossil frost fudge
galaxy garnet gazelle gecko ginger glacier glider globe gnome golden gopher granite grape gravel grotto guitar
hammock harbor harvest hazel helix hickory hollow honey horizon hornet igloo indigo ivory jasmine jasper jetty
jewel jigsaw jolly juniper kangaroo kayak kelp kernel kestrel kettle kiwi koala lagoon lantern larch lava
lemon lichen lilac lime linen lion lizard lobster lotus lynx maize mango maple marble marlin meadow
melon meteor mint mirror mitten mosaic moss moth mulch mustard nebula nectar needle nickel nimbus noble
nomad noodle nova nozzle nugget nutmeg oasis ocean octave olive onyx opal orbit orchid oregano osprey
otter oyster paddle palace pansy papaya parrot pasta pastel peach pebble pelican pepper petal pewter phoenix
piano pigeon pilot pine pirate piston pixel plaza plum pocket polar poppy prairie prism puffin puma
pumpkin puzzle quail quartz quiver rabbit raccoon radish raisin ranch raven ravine reef relic rhino ribbon
ridge river robin rocket rose rubble ruby rudder saffron sage salmon sand sapphire satin savanna scarlet
sequoia shadow shore signal silver slate sonnet sparrow spring spruce star storm summer sunset thistle thunder
"""
WORDLIST: Tuple[str, ...] = tuple(dict.fromkeys(_WORDLIST_RAW.split()))

# ---------------------------------------------------------------------
# Terminal colors / small output helpers
# ---------------------------------------------------------------------
_COLOR = sys.stdout.isatty() and os.environ.get("TERM") != "dumb"
if os.name == "nt":
    os.system("")  # enables ANSI escape processing on modern Windows terminals

RESET, BOLD, DIM = "\033[0m", "\033[1m", "\033[2m"
RED, GREEN, YELLOW, CYAN = "\033[31m", "\033[32m", "\033[33m", "\033[36m"


def c(text: str, color: str) -> str:
    """Wrap text in ANSI color if the terminal supports it."""
    return f"{color}{text}{RESET}" if _COLOR else text


def info(msg: str) -> None:
    print(c(f"[*] {msg}", CYAN))


def ok(msg: str) -> None:
    print(c(f"[+] {msg}", GREEN))


def warn(msg: str) -> None:
    print(c(f"[!] {msg}", YELLOW))


def fail(msg: str) -> None:
    print(c(f"[x] {msg}", RED))


# ---------------------------------------------------------------------
# Input helpers
# ---------------------------------------------------------------------
def clean(text: str) -> str:
    """Strip control characters and surrounding whitespace."""
    return _CTRL_RE.sub("", text).strip()


def ask(prompt: str, *, required: bool = False, max_len: int = 500,
        default: Optional[str] = None) -> str:
    """Prompt for a line of input with length cap and optional default."""
    while True:
        suffix = f" [{default}]" if default is not None else ""
        raw = input(f"{prompt}{suffix}: ").strip()
        if not raw and default is not None:
            return default
        if not raw and required:
            fail("A value is required.")
            continue
        if len(raw) > max_len:
            fail(f"Maximum {max_len} characters.")
            continue
        return clean(raw)


def ask_yn(prompt: str, default: bool = False) -> bool:
    hint = "Y/n" if default else "y/N"
    while True:
        raw = input(f"{prompt} [{hint}]: ").strip().lower()
        if not raw:
            return default
        if raw in ("y", "yes"):
            return True
        if raw in ("n", "no"):
            return False
        fail("Please answer y or n.")


def ask_int(prompt: str, default: int, lo: int, hi: int) -> int:
    while True:
        raw = input(f"{prompt} [{default}]: ").strip()
        if not raw:
            return default
        if raw.isdigit() and lo <= int(raw) <= hi:
            return int(raw)
        fail(f"Enter a number between {lo} and {hi}.")


def ask_hidden(prompt: str) -> str:
    return getpass.getpass(f"{prompt}: ")


def pause() -> None:
    input(c("\nPress Enter to continue...", DIM))


# ---------------------------------------------------------------------
# Time / formatting helpers
# ---------------------------------------------------------------------
def iso_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def age_str(iso: Optional[str]) -> str:
    """Humanized age of an ISO timestamp, e.g. '3d', '2mo', '1y'."""
    if not iso:
        return "?"
    try:
        dt = datetime.fromisoformat(iso)
    except ValueError:
        return "?"
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    days = (datetime.now(timezone.utc) - dt).days
    if days < 0:
        return "?"
    if days == 0:
        return "today"
    if days < 30:
        return f"{days}d"
    if days < 365:
        return f"{days // 30}mo"
    return f"{days // 365}y"


def trunc(text: str, width: int) -> str:
    return text if len(text) <= width else text[: width - 1] + "…"


def b64e(data: bytes) -> str:
    return base64.b64encode(data).decode("ascii")


def b64d(text: str) -> bytes:
    return base64.b64decode(text.encode("ascii"))


# ---------------------------------------------------------------------
# Crypto layer
# ---------------------------------------------------------------------
def default_kdf() -> Dict[str, Any]:
    """Strongest KDF parameters supported by this installation."""
    if HAVE_ARGON2:
        return {"name": "argon2id", **ARGON2_PARAMS}
    return {"name": "pbkdf2-sha256", "iterations": PBKDF2_ITERATIONS}


def derive_key(password: str, salt: bytes, kdf: Dict[str, Any]) -> bytearray:
    """Derive a 32-byte AES key from the master password."""
    pw = password.encode("utf-8")
    name = kdf.get("name", "")
    if name == "argon2id":
        if not HAVE_ARGON2:
            fail("This vault requires Argon2id. Upgrade: pip install -U cryptography")
            sys.exit(1)
        kdf_obj = Argon2id(
            salt=salt, length=32,
            iterations=int(kdf.get("iterations", 3)),
            lanes=int(kdf.get("lanes", 4)),
            memory_cost=int(kdf.get("memory_cost", 65_536)),
        )
    else:
        kdf_obj = PBKDF2HMAC(
            algorithm=hashes.SHA256(), length=32, salt=salt,
            iterations=int(kdf.get("iterations", PBKDF2_ITERATIONS)),
        )
    return bytearray(kdf_obj.derive(pw))


def encrypt(key: bytes, plaintext: bytes) -> bytes:
    """AES-256-GCM: returns nonce || ciphertext||tag, bound to AAD."""
    nonce = secrets.token_bytes(12)
    return nonce + AESGCM(key).encrypt(nonce, plaintext, AAD)


def decrypt(key: bytes, blob: bytes) -> bytes:
    """Authenticated decryption. Raises InvalidTag on wrong key/tamper."""
    if len(blob) < 13:
        raise ValueError("Ciphertext too short.")
    return AESGCM(key).decrypt(blob[:12], blob[12:], AAD)


# ---------------------------------------------------------------------
# Safe file handling
# ---------------------------------------------------------------------
def restrict_perms(path: str) -> None:
    try:
        if os.name == "posix":
            os.chmod(path, 0o600)
        else:
            os.chmod(path, stat.S_IREAD | stat.S_IWRITE)
    except OSError:
        pass


def atomic_write(path: str, data: bytes, keep_backup: bool = True) -> None:
    """Write bytes atomically; never leaves a truncated vault on disk."""
    directory = os.path.dirname(os.path.abspath(path)) or "."
    os.makedirs(directory, exist_ok=True)
    fd, tmp_path = tempfile.mkstemp(prefix=".seji_tmp_", dir=directory)
    try:
        with os.fdopen(fd, "wb") as fh:
            fh.write(data)
            fh.flush()
            os.fsync(fh.fileno())
        restrict_perms(tmp_path)
        if keep_backup and os.path.exists(path):
            shutil.copy2(path, path + ".bak")
            restrict_perms(path + ".bak")
        os.replace(tmp_path, path)
        tmp_path = None
    finally:
        if tmp_path is not None and os.path.exists(tmp_path):
            try:
                os.remove(tmp_path)
            except OSError:
                pass


# ---------------------------------------------------------------------
# Strength analysis
# ---------------------------------------------------------------------
def _has_run(text: str, run: int = 4) -> bool:
    """Detect ascending/descending character runs like 'abcd' or '4321'."""
    if len(text) < run:
        return False
    asc = desc = 1
    for prev, cur in zip(text, text[1:]):
        delta = ord(cur) - ord(prev)
        asc = asc + 1 if delta == 1 else 1
        desc = desc + 1 if delta == -1 else 1
        if asc >= run or desc >= run:
            return True
    return False


def _charset_size(pw: str) -> int:
    size = 0
    if any(ch in string.ascii_lowercase for ch in pw):
        size += 26
    if any(ch in string.ascii_uppercase for ch in pw):
        size += 26
    if any(ch in string.digits for ch in pw):
        size += 10
    if any(ch not in string.ascii_letters + string.digits for ch in pw):
        size += 33
    return size


def is_common_password(pw: str) -> bool:
    low = pw.lower()
    if low in COMMON_PASSWORDS:
        return True
    return bool(re.fullmatch(r"(?:password|admin|welcome|qwerty)\d*", low))


def estimate_bits(pw: str) -> float:
    """Rough entropy estimate with heuristic penalties."""
    if not pw:
        return 0.0
    cs = _charset_size(pw)
    bits = len(pw) * math.log2(cs) if cs else 0.0
    low = pw.lower()
    if low in COMMON_PASSWORDS:
        return min(bits, 5.0)
    weak_tokens = ("password", "qwerty", "admin", "letmein", "welcome",
                   "iloveyou", "abcd", "1234", "asdf")
    if any(tok in low for tok in weak_tokens):
        bits *= 0.6
    if _has_run(low):
        bits *= 0.7
    if len(set(pw)) <= len(pw) / 2:      # heavy repetition
        bits *= 0.7
    return max(0.0, bits)


def strength(pw: str) -> Tuple[float, str, int]:
    """Return (entropy bits, label, 0-4 score)."""
    bits = estimate_bits(pw)
    if bits < 28:
        return bits, "Very weak", 0
    if bits < 36:
        return bits, "Weak", 1
    if bits < 60:
        return bits, "Fair", 2
    if bits < 100:
        return bits, "Strong", 3
    return bits, "Excellent", 4


def print_strength(pw: str) -> None:
    bits, label, score = strength(pw)
    bar = ("#" * score).ljust(4, ".")
    color = (RED, RED, YELLOW, GREEN, GREEN)[score]
    extra = c("  [common password!]", RED) if is_common_password(pw) else ""
    print(f"  Strength: [{c(bar, color)}] {c(label, color)} "
          f"(~{bits:.0f} bits){extra}")


# ---------------------------------------------------------------------
# Generators (CSPRNG only)
# ---------------------------------------------------------------------
SYMBOLS = "!@#$%^&*-_=+?"
_AMBIGUOUS = set("Il1O0o")


def generate_password(length: int = 20, *, lower: bool = True, upper: bool = True,
                      digits: bool = True, symbols: bool = True,
                      exclude_ambiguous: bool = True) -> str:
    """Generate a password guaranteeing one char from each selected class."""
    pools: List[str] = []
    if lower:
        pools.append(string.ascii_lowercase)
    if upper:
        pools.append(string.ascii_uppercase)
    if digits:
        pools.append(string.digits)
    if symbols:
        pools.append(SYMBOLS)
    if not pools:
        raise ValueError("Select at least one character set.")
    if length < len(pools):
        raise ValueError(f"Length must be at least {len(pools)}.")

    if exclude_ambiguous:  # filter letters/digits, keep symbols intact
        filtered = []
        for idx, pool in enumerate(pools):
            if idx < 3:
                reduced = "".join(ch for ch in pool if ch not in _AMBIGUOUS)
                pool = reduced if reduced else pool
            filtered.append(pool)
        pools = filtered

    alphabet = "".join(pools)
    while True:
        chars = [secrets.choice(pool) for pool in pools]
        chars += [secrets.choice(alphabet) for _ in range(length - len(pools))]
        for i in range(len(chars) - 1, 0, -1):       # secure Fisher-Yates
            j = secrets.randbelow(i + 1)
            chars[i], chars[j] = chars[j], chars[i]
        pw = "".join(chars)
        if all(any(ch in pool for ch in pw) for pool in pools):
            return pw


def generate_passphrase(words: int = 6, sep: str = "-",
                        capitalize: bool = True, add_digits: bool = True) -> str:
    """Passphrase from the embedded wordlist (~8 bits/word, +~6.6 for 2 digits)."""
    parts: List[str] = []
    for i in range(words):
        digest = hashlib.sha256(secrets.token_bytes(32) + i.to_bytes(4, "big")).digest()
        idx = int.from_bytes(digest[:4], "big") % len(WORDLIST)
        word = WORDLIST[idx]
        parts.append(word.capitalize() if capitalize else word)
    if add_digits:
        parts.append(secrets.choice(string.digits) + secrets.choice(string.digits))
    return sep.join(parts)


# ---------------------------------------------------------------------
# Clipboard (dependency-free, auto-clear)
# ---------------------------------------------------------------------
_clip_timer: Optional[threading.Timer] = None


def _raw_clipboard_set(text: str) -> bool:
    if HAVE_PYPERCLIP:
        try:
            pyperclip.copy(text)
            return True
        except Exception:
            pass
    if os.name == "nt":
        return _clipboard_set_windows(text)
    if os.name == "posix":
        return _clipboard_set_posix(text)
    return False


def _clipboard_set_windows(text: str) -> bool:
    CF_UNICODETEXT, GMEM_MOVEABLE = 13, 0x0002
    user32 = ctypes.windll.user32
    kernel32 = ctypes.windll.kernel32
    if not user32.OpenClipboard(0):
        return False
    try:
        user32.EmptyClipboard()
        buf = text.encode("utf-16-le") + b"\x00\x00"
        handle = kernel32.GlobalAlloc(GMEM_MOVEABLE, len(buf))
        if not handle:
            return False
        ptr = kernel32.GlobalLock(handle)
        if not ptr:
            return False
        try:
            ctypes.memmove(ptr, buf, len(buf))
        finally:
            kernel32.GlobalUnlock(handle)
        user32.SetClipboardData(CF_UNICODETEXT, handle)
        return True
    finally:
        user32.CloseClipboard()


def _clipboard_set_posix(text: str) -> bool:
    for cmd in ("pbcopy", "wl-copy", "xclip -selection clipboard",
                "xsel --clipboard --input"):
        if shutil.which(cmd.split()[0]):
            try:
                subprocess.run(cmd.split(), input=text.encode("utf-8"),
                               check=True, timeout=5)
                return True
            except Exception:
                continue
    return False


def copy_to_clipboard(text: str, clear_after: int = CLIPBOARD_CLEAR_SECONDS) -> bool:
    """Copy text, scheduling an automatic clipboard wipe."""
    global _clip_timer
    if not _raw_clipboard_set(text):
        return False
    if clear_after > 0:
        if _clip_timer is not None:
            _clip_timer.cancel()
        _clip_timer = threading.Timer(clear_after, lambda: _raw_clipboard_set(""))
        _clip_timer.daemon = True
        _clip_timer.start()
    return True


# ---------------------------------------------------------------------
# Vault model
# ---------------------------------------------------------------------
def _normalize_entry(raw: Dict[str, Any]) -> Dict[str, Any]:
    now = iso_now()
    return {
        "id": str(raw.get("id") or secrets.token_hex(8)),
        "service": clean(str(raw.get("service", "")))[:100],
        "username": clean(str(raw.get("username", "")))[:200],
        "password": _CTRL_RE.sub("", str(raw.get("password", "")))[:MAX_ENTRY_LEN],
        "url": clean(str(raw.get("url", "")))[:500],
        "notes": clean(str(raw.get("notes", "")))[:MAX_ENTRY_LEN],
        "created_at": raw.get("created_at") or now,
        "updated_at": raw.get("updated_at") or now,
        "password_updated_at": raw.get("password_updated_at") or now,
    }


class Vault:
    """In-memory vault bound to a derived key; persists atomically."""

    def __init__(self, path: str, key: bytearray, kdf: Dict[str, Any],
                 salt: bytes, data: Dict[str, Any]) -> None:
        self.path = path
        self._key: Optional[bytearray] = key
        self.kdf = kdf
        self.salt = salt
        self.entries: List[Dict[str, Any]] = [_normalize_entry(e)
                                              for e in data.get("entries", [])]
        self.settings: Dict[str, Any] = {"autolock": DEFAULT_AUTOLOCK}
        self.settings.update(data.get("settings", {}) or {})

    # -- lifecycle -----------------------------------------------------
    @property
    def key(self) -> bytearray:
        if self._key is None:
            raise RuntimeError("Vault is locked.")
        return self._key

    @property
    def unlocked(self) -> bool:
        return self._key is not None

    def lock(self) -> None:
        if self._key is not None:
            self._key.clear()          # best-effort wipe
            self._key = None

    # -- persistence ---------------------------------------------------
    def save(self) -> None:
        payload = json.dumps({"entries": self.entries, "settings": self.settings},
                             ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        doc = {
            "version": VAULT_VERSION,
            "kdf": self.kdf,
            "salt": b64e(self.salt),
            "data": b64e(encrypt(bytes(self.key), payload)),
        }
        atomic_write(self.path, json.dumps(doc, indent=1).encode("utf-8"))

    # -- entries -------------------------------------------------------
    def unique_id(self) -> str:
        while True:
            candidate = secrets.token_hex(8)
            if all(e["id"] != candidate for e in self.entries):
                return candidate

    def find_duplicates(self, service: str, username: str) -> List[Dict[str, Any]]:
        s, u = service.lower(), username.lower()
        return [e for e in self.entries
                if e["service"].lower() == s and e["username"].lower() == u]

    def search(self, term: str) -> List[Dict[str, Any]]:
        needle = term.lower()
        return [e for e in self.entries if any(
            needle in (e.get(field, "") or "").lower()
            for field in ("service", "username", "url", "notes"))]


# ---------------------------------------------------------------------
# Vault creation / unlocking
# ---------------------------------------------------------------------
def load_vault_doc(path: str) -> Dict[str, Any]:
    try:
        with open(path, "rb") as fh:
            doc = json.loads(fh.read().decode("utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"Cannot read vault: {exc}")
        sys.exit(1)
    if not all(k in doc for k in ("version", "kdf", "salt", "data")):
        fail("Vault file is missing required fields (corrupted?).")
        sys.exit(1)
    if doc["version"] > VAULT_VERSION:
        fail(f"Vault was created by a newer version ({doc['version']}).")
        sys.exit(1)
    return doc


def check_file_perms(path: str) -> None:
    """Warn if a POSIX vault is readable by group/others."""
    if os.name != "posix":
        return
    try:
        mode = os.stat(path).st_mode
        if mode & 0o077:
            warn("Vault file is readable by other users. Fix with: "
                 f"chmod 600 {path}")
    except OSError:
        pass


def prompt_new_secret(kind: str = "master password") -> str:
    """Prompt (twice) for a new strong secret with live feedback."""
    while True:
        first = ask_hidden(f"New {kind} (min {MIN_MASTER_LEN} chars)")
        if len(first) < MIN_MASTER_LEN:
            fail(f"Must be at least {MIN_MASTER_LEN} characters.")
            continue
        if is_common_password(first):
            fail("That is a well-known weak password. Choose another.")
            continue
        print_strength(first)
        second = ask_hidden("Confirm")
        if first != second:
            fail("Passwords do not match. Try again.")
            continue
        bits, label, _ = strength(first)
        if bits < 40 and not ask_yn(
                f"Strength is only '{label}'. Use anyway?", default=False):
            continue
        return first


def create_vault_flow(path: str) -> Vault:
    print(c(f"\n  Welcome to {APP_NAME} — first run", BOLD))
    print(c(f"  Creating new vault: {path}\n", DIM))
    master = prompt_new_secret()
    kdf = default_kdf()
    salt = secrets.token_bytes(16)
    key = derive_key(master, salt, kdf)
    vault = Vault(path, key, kdf, salt, {"entries": [], "settings": {}})
    vault.save()
    ok(f"Vault created: {path}")
    if HAVE_ARGON2:
        info("Key derivation: Argon2id (3 passes, 64 MiB)")
    else:
        info(f"Key derivation: PBKDF2-SHA256 x{PBKDF2_ITERATIONS:,} "
             "(install cryptography>=43 for Argon2id)")
    return vault


def unlock_flow(path: str) -> Vault:
    doc = load_vault_doc(path)
    check_file_perms(path)
    kdf, salt = doc["kdf"], b64d(doc["salt"])
    kdf_name = kdf.get("name", "pbkdf2-sha256")
    print(c(f"  Vault: {path}  (KDF: {kdf_name})", DIM))

    for attempt in range(MAX_UNLOCK_ATTEMPTS):
        master = ask_hidden("Master password")
        if not master:
            continue
        key = derive_key(master, salt, kdf)
        try:
            payload = decrypt(bytes(key), b64d(doc["data"]))
        except InvalidTag:
            key.clear()
            delay = min(2 ** attempt, 30)
            fail(f"Wrong password or corrupted vault. Waiting {delay}s...")
            time.sleep(delay)
            continue
        except (ValueError, json.JSONDecodeError) as exc:
            key.clear()
            fail(f"Vault cannot be decrypted: {exc}")
            sys.exit(1)
        try:
            data = json.loads(payload.decode("utf-8"))
        except json.JSONDecodeError:
            key.clear()
            fail("Vault plaintext is corrupted.")
            sys.exit(1)
        ok(f"Unlocked — {len(data.get('entries', []))} entries.")
        return Vault(path, key, kdf, salt, data)

    fail("Too many failed attempts. Exiting.")
    sys.exit(2)


def change_master_flow(vault: Vault) -> None:
    current = ask_hidden("Current master password")
    test_key = derive_key(current, vault.salt, vault.kdf)
    match = hmac.compare_digest(bytes(test_key), bytes(vault.key))
    test_key.clear()
    if not match:
        fail("Current password is incorrect.")
        return
    new_master = prompt_new_secret("new master password")
    new_kdf = default_kdf()                       # rotate params too
    new_salt = secrets.token_bytes(16)
    new_key = derive_key(new_master, new_salt, new_kdf)
    vault.key.clear()
    vault._key = new_key                          # noqa: SLF001 (internal swap)
    vault.kdf, vault.salt = new_kdf, new_salt
    vault.save()
    ok("Master password changed. New salt + KDF parameters applied.")


# ---------------------------------------------------------------------
# UI: listing / selecting
# ---------------------------------------------------------------------
def print_entries(entries: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Print a numbered table (sorted by service); returns display order."""
    ordered = sorted(entries, key=lambda e: e["service"].lower())
    print()
    print(c(f"  {'#':>3}  {'Service':<26} {'Username':<20} {'Upd':>5}  Password",
            BOLD))
    print(c("  " + "-" * 74, DIM))
    for i, e in enumerate(ordered, 1):
        try:
            updated = datetime.fromisoformat(e["password_updated_at"])
            if updated.tzinfo is None:
                updated = updated.replace(tzinfo=timezone.utc)
            aged = (datetime.now(timezone.utc) - updated).days >= PASSWORD_AGE_WARN_DAYS
        except (ValueError, KeyError):
            aged = False
        marker = c(f"age>{PASSWORD_AGE_WARN_DAYS}d", YELLOW) if aged else c("ok", GREEN)
        print(f"  {i:>3}. {trunc(e['service'], 26):<26} "
              f"{trunc(e['username'] or '—', 20):<20} "
              f"{age_str(e['updated_at']):>5}  {marker}")
    print(c(f"  Total: {len(ordered)} entries", DIM))
    return ordered


def select_entry(vault: Vault, action: str) -> Optional[Dict[str, Any]]:
    if not vault.entries:
        warn("Vault is empty. Add an entry first.")
        return None
    ordered = print_entries(vault.entries)
    raw = ask(f"Number of entry to {action} (blank = cancel)")
    if not raw:
        return None
    if not raw.isdigit() or not (1 <= int(raw) <= len(ordered)):
        fail("Invalid selection.")
        return None
    return ordered[int(raw) - 1]


# ---------------------------------------------------------------------
# UI: entry actions
# ---------------------------------------------------------------------
def input_password(prompt: str = "Password") -> str:
    """Ask manual vs generated; returns a non-empty password."""
    while True:
        if ask_yn(f"Generate {prompt.lower()}?", default=True):
            length = ask_int("  Length", 20, MIN_GEN_LEN, 128)
            symbols = ask_yn("  Include symbols", True)
            no_lookalike = ask_yn("  Avoid look-alike chars (O/0, l/1/I)", True)
            try:
                pw = generate_password(length, symbols=symbols,
                                       exclude_ambiguous=no_lookalike)
            except ValueError as exc:
                fail(str(exc))
                continue
            print(f"  Generated: {c(BOLD + pw + RESET, CYAN)}")
            print_strength(pw)
            if ask_yn("  Use this password?", True):
                return pw
            continue
        pw = ask_hidden(prompt)
        if not pw:
            fail("Password cannot be empty.")
            continue
        if _CTRL_RE.search(pw):
            fail("Control characters are not allowed.")
            continue
        if len(pw) > MAX_ENTRY_LEN:
            fail(f"Maximum {MAX_ENTRY_LEN} characters.")
            continue
        print_strength(pw)
        if ask_yn("  Use this password?", True):
            return pw


def action_add(vault: Vault) -> None:
    print(c("\n── Add entry ──", BOLD))
    service = ask("Service / site (e.g. github.com)", required=True, max_len=100)
    username = ask("Username / email", max_len=200)
    if vault.find_duplicates(service, username):
        warn("An entry with this service + username already exists. "
             "Use Edit instead (nothing added).")
        return
    entry = _normalize_entry({
        "id": vault.unique_id(),
        "service": service,
        "username": username,
        "password": input_password(),
        "url": ask("URL (optional)", max_len=500),
        "notes": ask("Notes (optional)", max_len=MAX_ENTRY_LEN),
    })
    vault.entries.append(entry)
    vault.save()
    ok(f"Saved entry '{entry['service']}'.")


def action_view(vault: Vault) -> None:
    entry = select_entry(vault, "view")
    if entry is None:
        return
    while True:
        pw_age = age_str(entry["password_updated_at"])
        print(c(f"\n  Service : {entry['service']}", BOLD))
        print(f"  Username: {entry['username'] or '—'}")
        print(f"  URL     : {entry['url'] or '—'}")
        if entry["notes"]:
            print(f"  Notes   : {trunc(entry['notes'], 120)}")
        print(f"  Password: {c('******** (hidden)', DIM)}   "
              f"(unchanged {pw_age})")
        choice = ask("[s]how password / [c]opy password / "
                     "[u]copy username / Enter = back").lower()
        if choice == "s":
            print(f"  Password: {c(BOLD + entry['password'] + RESET, CYAN)}")
        elif choice == "c":
            if copy_to_clipboard(entry["password"]):
                ok(f"Copied to clipboard — clears in "
                   f"{CLIPBOARD_CLEAR_SECONDS}s. (Other apps may read it.)")
            else:
                fail("No clipboard mechanism available on this system.")
        elif choice == "u":
            if copy_to_clipboard(entry["username"]):
                ok("Username copied.")
            else:
                fail("No clipboard mechanism available.")
        else:
            return


def action_edit(vault: Vault) -> None:
    entry = select_entry(vault, "edit")
    if entry is None:
        return
    fields = (("1", "Service", "service", 100),
              ("2", "Username", "username", 200),
              ("3", "URL", "url", 500),
              ("4", "Notes", "notes", MAX_ENTRY_LEN))
    while True:
        print(c(f"\n  Editing '{entry['service']}' ({entry['username'] or '—'})",
                BOLD))
        for key, label, _, _ in fields:
            print(f"  [{key}] {label}: {trunc(entry[key], 60) or '—'}")
        print("  [5] Password      [0] Done")
        choice = ask("Field to edit").lower()
        if choice == "0":
            return
        if choice == "5":
            entry["password"] = input_password("New password")
            entry["password_updated_at"] = iso_now()
        else:
            match = next((f for f in fields if f[0] == choice), None)
            if match is None:
                fail("Invalid choice.")
                continue
            _, label, field, max_len = match
            entry[field] = ask(f"New {label}", max_len=max_len,
                               default=entry[field])
        entry["updated_at"] = iso_now()
        vault.save()
        ok("Saved.")


def action_delete(vault: Vault) -> None:
    entry = select_entry(vault, "delete")
    if entry is None:
        return
    print(c(f"  Deleting '{entry['service']}' ({entry['username'] or '—'})",
            YELLOW))
    confirm = ask(f"Type the service name exactly to confirm")
    if confirm != entry["service"]:
        fail("Confirmation did not match — nothing deleted.")
        return
    vault.entries.remove(entry)
    vault.save()
    ok(f"Deleted '{entry['service']}'. A pre-delete copy is in "
       f"{vault.path}.bak")


def action_search(vault: Vault) -> None:
    term = ask("Search term", required=True, max_len=100)
    matches = vault.search(term)
    if not matches:
        warn("No matches.")
        return
    ordered = print_entries(matches)
    raw = ask("Number to view (blank = back)")
    if raw.isdigit() and 1 <= int(raw) <= len(ordered):
        # reuse view on the chosen entry
        fake_vault = vault  # view only needs entries list via select? use direct
        entry = ordered[int(raw) - 1]
        show_entry_detail(entry)


def show_entry_detail(entry: Dict[str, Any]) -> None:
    """Simple view+copy for search results."""
    while True:
        print(c(f"\n  Service : {entry['service']}", BOLD))
        print(f"  Username: {entry['username'] or '—'}")
        print(f"  URL     : {entry['url'] or '—'}")
        if entry["notes"]:
            print(f"  Notes   : {trunc(entry['notes'], 120)}")
        choice = ask("[s]how password / [c]opy password / Enter = back").lower()
        if choice == "s":
            print(f"  Password: {c(BOLD + entry['password'] + RESET, CYAN)}")
        elif choice == "c":
            if copy_to_clipboard(entry["password"]):
                ok(f"Copied — clears in {CLIPBOARD_CLEAR_SECONDS}s.")
            else:
                fail("No clipboard mechanism available.")
        else:
            return


# ---------------------------------------------------------------------
# UI: password tools / backups / settings
# ---------------------------------------------------------------------
def action_password_tools() -> None:
    while True:
        print(c("\n── Password tools ──", BOLD))
        print("  [1] Generate password")
        print("  [2] Generate passphrase")
        print("  [3] Check strength of a password")
        print("  [0] Back")
        choice = ask("Choice").lower()
        if choice == "0":
            return
        if choice == "1":
            length = ask_int("  Length", 20, MIN_GEN_LEN, 128)
            symbols = ask_yn("  Include symbols", True)
            no_lookalike = ask_yn("  Avoid look-alike chars", True)
            try:
                pw = generate_password(length, symbols=symbols,
                                       exclude_ambiguous=no_lookalike)
            except ValueError as exc:
                fail(str(exc))
                continue
            print(f"\n  Password : {c(BOLD + pw + RESET, CYAN)}")
            print_strength(pw)
            if ask_yn("  Copy to clipboard?", False) and copy_to_clipboard(pw):
                ok(f"Copied — clears in {CLIPBOARD_CLEAR_SECONDS}s.")
        elif choice == "2":
            words = ask_int("  Word count (8 bits each)", 6, 3, 12)
            add_digits = ask_yn("  Append 2 digits (+~7 bits)", True)
            sep = ask("  Separator", default="-", max_len=3) or "-"
            pp = generate_passphrase(words, sep=sep, add_digits=add_digits)
            bits = words * math.log2(len(WORDLIST)) + (6.6 if add_digits else 0)
            print(f"\n  Passphrase: {c(BOLD + pp + RESET, CYAN)}")
            print(f"  (~{bits:.0f} bits, {len(WORDLIST)}-word list)")
            if ask_yn("  Copy to clipboard?", False) and copy_to_clipboard(pp):
                ok(f"Copied — clears in {CLIPBOARD_CLEAR_SECONDS}s.")
        elif choice == "3":
            pw = ask_hidden("Password to check (input hidden)")
            print_strength(pw)


def action_export(vault: Vault) -> None:
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    default_path = os.path.join(os.path.expanduser("~"),
                                f"seji_backup_{stamp}.seji")
    path = ask("Backup file", default=default_path, max_len=300)
    if os.path.exists(path) and not ask_yn("File exists. Overwrite?", False):
        warn("Export cancelled.")
        return
    print(c("  The backup is encrypted with its own passphrase.", DIM))
    backup_pw = prompt_new_secret("backup passphrase")
    kdf = default_kdf()
    salt = secrets.token_bytes(16)
    key = derive_key(backup_pw, salt, kdf)
    payload = json.dumps({
        "entries": vault.entries,
        "settings": vault.settings,
        "exported_at": iso_now(),
        "app": f"{APP_NAME} {VERSION}",
    }, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    doc = {"format": "seji-backup", "version": 1, "kdf": kdf,
           "salt": b64e(salt), "data": b64e(encrypt(bytes(key), payload))}
    atomic_write(path, json.dumps(doc, indent=1).encode("utf-8"))
    key.clear()
    ok(f"Encrypted backup written: {path}")
    warn("Store this file somewhere safe — it contains all your secrets.")


def action_import(vault: Vault) -> None:
    path = ask("Backup file to import", required=True, max_len=300)
    if not os.path.exists(path):
        fail("File not found.")
        return
    try:
        with open(path, "rb") as fh:
            doc = json.loads(fh.read().decode("utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"Cannot read backup: {exc}")
        return
    if doc.get("format") != "seji-backup":
        fail("Not a Seji backup file.")
        return
    pw = ask_hidden("Backup passphrase")
    try:
        key = derive_key(pw, b64d(doc["salt"]), doc["kdf"])
        payload = decrypt(bytes(key), b64d(doc["data"]))
        key.clear()
        data = json.loads(payload.decode("utf-8"))
    except InvalidTag:
        fail("Wrong passphrase or corrupted backup.")
        return
    except (ValueError, json.JSONDecodeError) as exc:
        fail(f"Backup cannot be read: {exc}")
        return

    added = skipped = 0
    for raw in data.get("entries", []):
        entry = _normalize_entry(raw)
        if vault.find_duplicates(entry["service"], entry["username"]):
            skipped += 1
            continue
        entry["id"] = vault.unique_id()
        vault.entries.append(entry)
        added += 1
    vault.save()
    ok(f"Import finished: {added} added, {skipped} duplicates skipped.")


def action_settings(vault: Vault) -> None:
    print(c("\n── Settings ──", BOLD))
    print(f"  Auto-lock: {vault.settings.get('autolock', DEFAULT_AUTOLOCK)}s "
          f"(0 = disabled)")
    seconds = ask_int("  New auto-lock seconds", 
                      int(vault.settings.get("autolock", DEFAULT_AUTOLOCK)),
                      0, 3600)
    vault.settings["autolock"] = seconds
    vault.save()
    ok("Settings saved.")


# ---------------------------------------------------------------------
# Main menu loop
# ---------------------------------------------------------------------
class SessionLocked(Exception):
    """Raised to return control to the unlock screen."""


MENU = """
 [1] List entries     [2] Add entry       [3] View / copy
 [4] Edit entry       [5] Delete entry    [6] Search
 [7] Password tools   [8] Change master   [9] Export backup
 [10] Import backup   [11] Settings       [12] Lock now
 [0] Quit"""


def run_menu(vault: Vault) -> None:
    """Interactive loop. Returns on quit; raises SessionLocked on lock."""
    autolock = int(vault.settings.get("autolock", DEFAULT_AUTOLOCK))
    last_activity = time.monotonic()

    def list_and_pause() -> None:
        print_entries(vault.entries)
        pause()

    def password_tools() -> None:
        action_password_tools()

    # Every handler that needs the vault is wrapped in a lambda
    # that closes over it, so handler() can be called uniformly.
    dispatch = {
        "1": list_and_pause,
        "2": lambda: action_add(vault),
        "3": lambda: action_view(vault),
        "4": lambda: action_edit(vault),
        "5": lambda: action_delete(vault),
        "6": lambda: action_search(vault),
        "7": password_tools,
        "8": lambda: change_master_flow(vault),
        "9": lambda: action_export(vault),
        "10": lambda: action_import(vault),
        "11": lambda: action_settings(vault),
    }

    while True:
        if vault.unlocked and autolock > 0 and \
                time.monotonic() - last_activity > autolock:
            vault.lock()
            raise SessionLocked

        print(c(MENU, DIM))
        choice = ask("Choice", max_len=4).strip().lower()

        if choice == "0":
            vault.lock()
            print(c("\nVault locked. Goodbye. 👋", CYAN))
            return
        if choice == "12":
            vault.lock()
            raise SessionLocked

        handler = dispatch.get(choice)
        if handler is None:
            fail("Unknown choice.")
            continue
        try:
            handler()
        except Exception as exc:  # keep session alive on single-action errors
            fail(f"Action failed: {exc}")
        last_activity = time.monotonic()


def print_banner() -> None:
    print(c("=" * 56, CYAN))
    print(c(f"   {APP_NAME} v{VERSION}   —  offline • encrypted • yours",
            BOLD + CYAN))
    print(c("=" * 56, CYAN))
    kdf_note = "Argon2id" if HAVE_ARGON2 else "PBKDF2-SHA256"
    print(c(f"   Crypto: AES-256-GCM • KDF: {kdf_note} • CSPRNG only", DIM))
    print()


def main() -> None:
    parser = argparse.ArgumentParser(
        prog="passman",
        description=f"{APP_NAME} — single-file encrypted password manager.")
    parser.add_argument("vault", nargs="?", default=DEFAULT_VAULT,
                        help="vault file path (default: ~/.seji_vault.json)")
    parser.add_argument("--version", action="version",
                        version=f"{APP_NAME} {VERSION}")
    args = parser.parse_args()

    print_banner()
    path = os.path.abspath(os.path.expanduser(args.vault))

    vault = create_vault_flow(path) if not os.path.exists(path) \
        else unlock_flow(path)

    while True:
        try:
            run_menu(vault)
            return
        except SessionLocked:
            warn("\nSession locked (inactivity or manual lock).")
            vault = unlock_flow(path)
        except (EOFError, KeyboardInterrupt):
            vault.lock()
            print(c("\nInterrupted — vault locked. Goodbye.", CYAN))
            return


if __name__ == "__main__":
    main()
