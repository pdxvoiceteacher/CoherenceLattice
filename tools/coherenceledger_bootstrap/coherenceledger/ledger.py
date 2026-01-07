from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Tuple

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

from .schemas import LedgerEvent
from .did import DidKey
from .crypto import b64encode, b64decode, load_public_key_raw


class LedgerError(RuntimeError):
    pass


@dataclass
class Ledger:
    """An append-only JSONL ledger of signed, hash-chained events."""
    path: Path

    def _read_lines(self) -> List[str]:
        if not self.path.exists():
            return []
        return self.path.read_text(encoding="utf-8").splitlines()

    def read_events(self) -> List[LedgerEvent]:
        events: List[LedgerEvent] = []
        for line in self._read_lines():
            if not line.strip():
                continue
            d = json.loads(line)
            events.append(LedgerEvent.from_dict(d))
        return events

    def last_seal(self) -> Optional[str]:
        events = self.read_events()
        return events[-1].seal if events else None

    def append(self, event: LedgerEvent) -> None:
        # Minimal checks before writing
        existing_last = self.last_seal()
        if event.prev_seal != existing_last:
            raise LedgerError(f"prev_seal mismatch: event.prev_seal={event.prev_seal} ledger_last={existing_last}")
        line = json.dumps(event.to_dict(), ensure_ascii=False, separators=(",", ":"), sort_keys=True)
        with self.path.open("a", encoding="utf-8") as f:
            f.write(line + "\n")

    def verify(self) -> None:
        """Verify hash chain integrity and signatures for all events."""
        events = self.read_events()
        prev: Optional[str] = None
        for idx, ev in enumerate(events):
            if ev.prev_seal != prev:
                raise LedgerError(f"Chain break at index {idx}: expected prev_seal={prev}, got {ev.prev_seal}")
            # Verify signature
            pub = self._resolve_public_key(ev)
            pub.verify(b64decode(ev.signature), ev.signing_payload())
            prev = ev.seal

    def _resolve_public_key(self, ev: LedgerEvent) -> Ed25519PublicKey:
        # Prefer explicit pubkey hint if present
        if ev.public_key_b64:
            return load_public_key_raw(b64decode(ev.public_key_b64))
        # else resolve from did:key
        dk = DidKey.parse(ev.actor_did)
        return load_public_key_raw(dk.public_key_bytes)
