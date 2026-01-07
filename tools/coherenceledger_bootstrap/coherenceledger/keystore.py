from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey, Ed25519PublicKey

from .crypto import Ed25519Keypair, b64encode, b64decode, load_private_key_raw, load_public_key_raw
from .did import DidKey


@dataclass
class KeyStore:
    """Very small local keystore for did:key Ed25519 keys.

    File format is JSON with base64url fields. Keep this file private.
    """
    path: Path

    def exists(self) -> bool:
        return self.path.exists()

    def generate(self, overwrite: bool = False) -> DidKey:
        if self.exists() and not overwrite:
            raise FileExistsError(str(self.path))
        kp = Ed25519Keypair.generate()
        did = DidKey.from_public_key(kp.public_bytes_raw())
        doc = {
            "type": "ed25519",
            "did": did.did,
            "private_key_b64": b64encode(kp.private_bytes_raw()),
            "public_key_b64": b64encode(kp.public_bytes_raw()),
        }
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(json.dumps(doc, indent=2, sort_keys=True), encoding="utf-8")
        return did

    def load_keypair(self) -> tuple[DidKey, Ed25519Keypair]:
        doc = json.loads(self.path.read_text(encoding="utf-8"))
        sk = load_private_key_raw(b64decode(doc["private_key_b64"]))
        pk = load_public_key_raw(b64decode(doc["public_key_b64"]))
        did = DidKey.parse(doc["did"])
        return did, Ed25519Keypair(private_key=sk, public_key=pk)
