import json
from pathlib import Path
import importlib.util
import pytest

pytest.importorskip("coherenceledger")

from coherenceledger.keystore import KeyStore
from ucc.vc_issuer import issue_vc, vc_sha256
from ucc.vc_registry import load_registry, save_registry, add_vc, revoke_vc, is_revoked


def test_issue_and_registry_roundtrip(tmp_path: Path):
    repo = tmp_path / "repo"
    repo.mkdir()
    (repo / ".secrets").mkdir()
    ks_path = repo / ".secrets" / "ks.json"
    KeyStore(path=ks_path).generate()

    issuer_did, _ = KeyStore(path=ks_path).load_keypair()

    vc = issue_vc(
        issuer_did=issuer_did.did,
        subject_did="did:key:subject123",
        types=["MemberCredential"],
        subject_claims={"role":"member"},
        keystore_path=ks_path,
    )
    assert vc["issuer"] == issuer_did.did
    assert vc_sha256(vc)

    reg_path = repo / "vc_registry.json"
    reg = load_registry(reg_path)
    add_vc(reg, vc)
    save_registry(reg_path, reg)

    reg2 = load_registry(reg_path)
    assert len(reg2["entries"]) == 1

    revoke_vc(reg2, vc["id"], "test")
    assert is_revoked(reg2, vc["id"]) is True
