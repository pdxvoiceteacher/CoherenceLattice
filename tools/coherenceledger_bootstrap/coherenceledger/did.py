"""DID utilities (focused on did:key for Ed25519).

DID Core describes DIDs as globally unique identifiers decoupled from centralized registries,
and DID methods define how to create/resolve them. We implement did:key locally for offline use.
"""

from __future__ import annotations

from dataclasses import dataclass

from .base58 import b58encode, b58decode

# Multicodec prefix for Ed25519 public key per did:key method
# ed25519-pub = 0xED 0x01
_ED25519_PUB_PREFIX = bytes([0xED, 0x01])


@dataclass(frozen=True)
class DidKey:
    did: str
    public_key_bytes: bytes  # raw Ed25519 pubkey (32 bytes)

    @staticmethod
    def from_public_key(public_key_bytes: bytes) -> "DidKey":
        if len(public_key_bytes) != 32:
            raise ValueError("Ed25519 public key must be 32 bytes (raw).")
        multicodec = _ED25519_PUB_PREFIX + public_key_bytes
        mb = "z" + b58encode(multicodec)  # multibase base58btc uses 'z' prefix
        did = f"did:key:{mb}"
        return DidKey(did=did, public_key_bytes=public_key_bytes)

    @staticmethod
    def parse(did: str) -> "DidKey":
        if not did.startswith("did:key:"):
            raise ValueError("Only did:key is supported by this helper.")
        mb = did[len("did:key:") :]
        if not mb.startswith("z"):
            raise ValueError("Only multibase base58btc (z...) is supported.")
        multicodec = b58decode(mb[1:])
        if not multicodec.startswith(_ED25519_PUB_PREFIX):
            raise ValueError("did:key multicodec prefix mismatch (expected Ed25519 pub).")
        pk = multicodec[len(_ED25519_PUB_PREFIX) :]
        if len(pk) != 32:
            raise ValueError("Ed25519 public key decoded from did:key must be 32 bytes.")
        return DidKey(did=did, public_key_bytes=pk)
