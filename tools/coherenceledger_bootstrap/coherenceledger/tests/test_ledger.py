from __future__ import annotations

import json
from pathlib import Path

import pytest

from coherenceledger.keystore import KeyStore
from coherenceledger.did import DidKey
from coherenceledger.ledger import Ledger, LedgerError
from coherenceledger.anchor import anchor_ucc_audit_bundle


def test_did_key_roundtrip(tmp_path: Path):
    ks_path = tmp_path / "ks.json"
    did = KeyStore(ks_path).generate()
    parsed = DidKey.parse(did.did)
    assert parsed.did == did.did
    assert len(parsed.public_key_bytes) == 32


def test_anchor_and_verify(tmp_path: Path):
    # Setup key
    ks_path = tmp_path / "ks.json"
    KeyStore(ks_path).generate()

    # Create fake audit bundle
    audit = tmp_path / "audit_bundle.json"
    audit.write_text(json.dumps({"git_commit": "abc123", "hashes": {"x": "y"}}), encoding="utf-8")

    ledger_path = tmp_path / "ledger.jsonl"
    res = anchor_ucc_audit_bundle(
        ledger_path=ledger_path,
        keystore_path=ks_path,
        audit_bundle_path=audit,
        repo_root=tmp_path,
    )
    assert res.ledger_path.exists()

    ledger = Ledger(ledger_path)
    ledger.verify()

    events = ledger.read_events()
    assert len(events) == 1
    assert events[0].prev_seal is None
    assert events[0].event_type == "ucc.audit_bundle.anchor"


def test_tamper_detection(tmp_path: Path):
    ks_path = tmp_path / "ks.json"
    KeyStore(ks_path).generate()
    audit = tmp_path / "audit_bundle.json"
    audit.write_text(json.dumps({"git_commit": "abc123"}), encoding="utf-8")

    ledger_path = tmp_path / "ledger.jsonl"
    anchor_ucc_audit_bundle(
        ledger_path=ledger_path,
        keystore_path=ks_path,
        audit_bundle_path=audit,
    )

    # Tamper with the ledger line
    lines = ledger_path.read_text(encoding="utf-8").splitlines()
    d = json.loads(lines[0])
    d["payload"]["git_commit"] = "evil"
    lines[0] = json.dumps(d, separators=(",", ":"), sort_keys=True)
    ledger_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    with pytest.raises(Exception):
        Ledger(ledger_path).verify()
