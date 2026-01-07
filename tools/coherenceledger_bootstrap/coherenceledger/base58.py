"""Minimal base58btc encode/decode (Bitcoin alphabet).

We implement this locally to avoid extra dependencies. This supports did:key multibase 'z'.
"""

from __future__ import annotations

from typing import Final


_ALPHABET: Final[str] = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
_ALPHABET_IDX: Final[dict[str, int]] = {c: i for i, c in enumerate(_ALPHABET)}


def b58encode(data: bytes) -> str:
    if not data:
        return ""
    # Count leading zero bytes.
    n_zeros = 0
    for b in data:
        if b == 0:
            n_zeros += 1
        else:
            break

    # Convert bytes to integer.
    num = int.from_bytes(data, "big")

    # Encode to base58.
    enc = []
    while num > 0:
        num, rem = divmod(num, 58)
        enc.append(_ALPHABET[rem])
    enc.reverse()

    return ("1" * n_zeros) + "".join(enc)


def b58decode(s: str) -> bytes:
    if not s:
        return b""

    # Count leading ones (zero bytes).
    n_zeros = 0
    for c in s:
        if c == "1":
            n_zeros += 1
        else:
            break

    num = 0
    for c in s:
        if c not in _ALPHABET_IDX:
            raise ValueError(f"Invalid base58 character: {c!r}")
        num = num * 58 + _ALPHABET_IDX[c]

    # Convert integer to bytes
    full = num.to_bytes((num.bit_length() + 7) // 8 or 1, "big")
    # Strip possible leading zero from int->bytes conversion if num=0
    if num == 0:
        full = b""
    return (b"\x00" * n_zeros) + full
