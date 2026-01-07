from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from .schemas import LedgerEvent
from .ledger import Ledger
from .keystore import KeyStore
from .crypto import b64encode
from .ucc_anchor import build_ucc_anchor_payload


@dataclass
class AnchorResult:
    ledger_path: Path
    event_id: str
    seal: str


def anchor_ucc_audit_bundle(
    *,
    ledger_path: Path,
    keystore_path: Path,
    audit_bundle_path: Path,
    report_json_path: Optional[Path] = None,
    repo_root: Optional[Path] = None,
    purpose: str = "ucc.audit.anchor",
) -> AnchorResult:
    """Anchor a UCC audit_bundle.json into a signed, hash-chained ledger."""
    ledger = Ledger(path=ledger_path)
    ks = KeyStore(path=keystore_path)
    did, kp = ks.load_keypair()

    payload = build_ucc_anchor_payload(
        audit_bundle_path=audit_bundle_path,
        report_json_path=report_json_path,
        repo_root=repo_root,
    )

    ev = LedgerEvent.create_unsigned(
        actor_did=did.did,
        purpose=purpose,
        event_type="ucc.audit_bundle.anchor",
        payload=payload,
        prev_seal=ledger.last_seal(),
    )

    sig = kp.sign(ev.signing_payload())
    ev.signature = b64encode(sig)
    ev.public_key_b64 = b64encode(kp.public_bytes_raw())

    ledger.append(ev)
    # Immediate verification of whole chain (fast for small ledgers)
    ledger.verify()

    return AnchorResult(ledger_path=ledger_path, event_id=ev.event_id, seal=ev.seal)
