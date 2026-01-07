from __future__ import annotations

import hashlib
from typing import Any

from . import jcs


def sha256_bytes(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_json(obj: Any) -> str:
    return sha256_hex(jcs.dumps(obj).encode("utf-8"))
