from __future__ import annotations

from typing import Tuple
from ucc.base58btc import b58decode

ED25519_PUB_PREFIX = bytes([0xED, 0x01])


def _read_uvarint(buf: bytes, i: int = 0) -> Tuple[int, int]:
    x = 0
    s = 0
    while True:
        if i >= len(buf):
            raise ValueError("varint overflow")
        b = buf[i]
        i += 1
        x |= (b & 0x7f) << s
        if (b & 0x80) == 0:
            return x, i
        s += 7
        if s > 63:
            raise ValueError("varint too large")


def did_key_to_ed25519_pubkey_bytes(did: str) -> bytes:
    """
    Supports did:key for Ed25519 public keys.

    did:key uses multibase base58btc: did:key:z...
    The decoded bytes often start with multicodec prefix for ed25519-pub:
      0xED 0x01 + 32-byte public key
    """
    if not isinstance(did, str) or not did.startswith("did:key:"):
        raise ValueError("not a did:key DID")
    mb = did[len("did:key:"):]
    if not mb or mb[0] != "z":
        raise ValueError("did:key must be multibase base58btc (z...)")

    raw = b58decode(mb[1:])

    # Common encoding: direct 2-byte multicodec prefix (0xED 0x01)
    if len(raw) >= 2 and raw[:2] == ED25519_PUB_PREFIX:
        pk = raw[2:]
        if len(pk) != 32:
            raise ValueError("ed25519 public key must be 32 bytes")
        return pk

    # Fallback: varint-decoded multicodec code (rare in our ecosystem)
    code, idx = _read_uvarint(raw, 0)
    if code in (0x01ED,):  # ed25519-pub
        pk = raw[idx:]
        if len(pk) != 32:
            raise ValueError("ed25519 public key must be 32 bytes")
        return pk

    raise ValueError(f"unsupported did:key multicodec prefix: {raw[:4].hex()}")
