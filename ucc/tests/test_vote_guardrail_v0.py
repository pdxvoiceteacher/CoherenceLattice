import json
from pathlib import Path
import importlib.util

import pytest

from ucc.vote_manifest import build_vote_manifest, write_vote_manifest
from ucc.vote_guardrail import audit_vote_manifest, write_guardrail


def test_guardrail_pass_org_open(tmp_path: Path):
    outdir = tmp_path / "vote"
    m = build_vote_manifest(
        title="M",
        purpose_id="p",
        purpose_statement="s",
        scope="org.governance",
        anonymity_mode="open",
        tally_mode="plaintext",
        weighting_mode="one_person_one_vote",
        electorate_type="did_vc",
        electorate_rules={"issuer":"UVLM","vc_type":"MemberCredential"},
    )
    mp = write_vote_manifest(outdir=outdir, manifest=m, sign=False, anchor=False)
    manifest = json.loads(mp.read_text(encoding="utf-8"))

    rep = audit_vote_manifest(manifest, manifest_sha256=mp.read_bytes().hex()[:64], strict=True)
    assert rep["passed"] is True


def test_guardrail_fail_public_open(tmp_path: Path):
    outdir = tmp_path / "vote"
    m = build_vote_manifest(
        title="M",
        purpose_id="p",
        purpose_statement="s",
        scope="public.deliberation",
        anonymity_mode="open",       # forbidden by policy
        tally_mode="plaintext",      # forbidden by policy
        weighting_mode="one_person_one_vote",
        electorate_type="did_vc",
        electorate_rules={"issuer":"UVLM","vc_type":"MemberCredential"},
    )
    mp = write_vote_manifest(outdir=outdir, manifest=m, sign=False, anchor=False)
    manifest = json.loads(mp.read_text(encoding="utf-8"))

    # correct manifest sha for audit (use real sha)
    import hashlib
    msha = hashlib.sha256(mp.read_bytes()).hexdigest()
    rep = audit_vote_manifest(manifest, manifest_sha256=msha, strict=True)
    assert rep["passed"] is False
    assert any(v["code"].startswith("anonymity") or v["code"].startswith("anonymity.") for v in rep["violations"])


@pytest.mark.skipif(importlib.util.find_spec("coherenceledger") is None, reason="coherenceledger not installed")
def test_guardrail_can_sign_and_anchor(tmp_path: Path):
    from coherenceledger.keystore import KeyStore
    from coherenceledger.ledger import Ledger

    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    (repo_root / ".secrets").mkdir()
    keystore = repo_root / ".secrets" / "coherenceledger_keystore.json"
    ledger = repo_root / "ledger.jsonl"

    ks = KeyStore(path=keystore)
    ks.generate()

    outdir = tmp_path / "vote2"
    m = build_vote_manifest(
        title="M2",
        purpose_id="p2",
        purpose_statement="s2",
        scope="org.governance",
        anonymity_mode="open",
        tally_mode="plaintext",
        weighting_mode="one_person_one_vote",
        electorate_type="did_vc",
        electorate_rules={"issuer":"UVLM","vc_type":"MemberCredential"},
    )
    mp = write_vote_manifest(outdir=outdir, manifest=m, sign=False, anchor=False, repo_root=repo_root, keystore_path=keystore, ledger_path=ledger)

    paths = write_guardrail(
        outdir=outdir,
        manifest_path=mp,
        strict=True,
        sign=True,
        anchor=True,
        repo_root=repo_root,
        keystore_path=keystore,
        ledger_path=ledger,
        ledger_purpose="ucc.vote_guardrail.anchor",
    )

    assert paths["report"].exists()
    assert paths["audit_bundle"].exists()

    L = Ledger(path=ledger)
    L.verify()
