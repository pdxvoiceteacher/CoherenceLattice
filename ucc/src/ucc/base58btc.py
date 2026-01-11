from __future__ import annotations

ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
INDEX = {c: i for i, c in enumerate(ALPHABET)}

def b58decode(s: str) -> bytes:
    if not isinstance(s, str) or not s:
        raise ValueError("empty base58 string")
    n = 0
    for ch in s:
        if ch not in INDEX:
            raise ValueError(f"invalid base58 char: {ch}")
        n = n * 58 + INDEX[ch]
    # Convert int to bytes
    b = n.to_bytes((n.bit_length() + 7) // 8, "big") if n > 0 else b""
    # Leading zeros
    pad = 0
    for ch in s:
        if ch == "1":
            pad += 1
        else:
            break
    return b"\x00" * pad + b
