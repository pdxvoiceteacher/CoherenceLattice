from __future__ import annotations

from dataclasses import dataclass, asdict
from datetime import datetime, timezone
from typing import Any, Dict, Optional
from uuid import uuid4

from . import jcs
from .hashing import sha256_hex
from .crypto import b64encode, b64decode


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


@dataclass
class LedgerEvent:
    """A signed, hash-chained ledger event (an append-only mini-block).

    This is designed to be:
    - deterministic (canonical JSON)
    - tamper-evident (prev_seal + seal)
    - attributable (actor_did + signature)
    """

    version: int
    event_id: str
    created_at: str
    actor_did: str
    purpose: str
    event_type: str
    payload: Dict[str, Any]
    payload_hash: str
    prev_seal: Optional[str]
    seal: str
    signature: str  # base64url
    # Optional hint for verifiers (DID can also resolve to pubkey)
    public_key_b64: Optional[str] = None

    @staticmethod
    def create_unsigned(
        *,
        actor_did: str,
        purpose: str,
        event_type: str,
        payload: Dict[str, Any],
        prev_seal: Optional[str],
    ) -> "LedgerEvent":
        payload_hash = sha256_hex(jcs.dumps(payload).encode("utf-8"))
        body = {
            "version": 1,
            "event_id": str(uuid4()),
            "created_at": _utc_now_iso(),
            "actor_did": actor_did,
            "purpose": purpose,
            "event_type": event_type,
            "payload": payload,
            "payload_hash": payload_hash,
            "prev_seal": prev_seal,
        }
        seal = sha256_hex(jcs.dumps(body).encode("utf-8"))
        return LedgerEvent(
            version=1,
            event_id=body["event_id"],
            created_at=body["created_at"],
            actor_did=actor_did,
            purpose=purpose,
            event_type=event_type,
            payload=payload,
            payload_hash=payload_hash,
            prev_seal=prev_seal,
            seal=seal,
            signature="",
            public_key_b64=None,
        )

    def signing_payload(self) -> bytes:
        body = {
            "version": self.version,
            "event_id": self.event_id,
            "created_at": self.created_at,
            "actor_did": self.actor_did,
            "purpose": self.purpose,
            "event_type": self.event_type,
            "payload": self.payload,
            "payload_hash": self.payload_hash,
            "prev_seal": self.prev_seal,
            "seal": self.seal,
        }
        return jcs.dumps(body).encode("utf-8")

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> "LedgerEvent":
        return LedgerEvent(**d)
