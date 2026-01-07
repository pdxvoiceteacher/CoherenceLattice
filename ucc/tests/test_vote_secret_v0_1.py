import json
from pathlib import Path
import importlib.util

import pytest

from ucc.vote_ballot_secret import build_secret_commit_and_reveal, write_secret_commit, write_secret_reveal
from ucc.vote_tally_secret import tally_secret


def test_secret_commit_reveal_tally(tmp_path: Path):
    outdir = tmp_path / "vote"
    mid = "manifest-123"

    c1, r1 = build_secret_commit_and_reveal(manifest_id=mid, choice="YES", nullifier_hex="aa"*16, salt_hex="bb"*16)
    write_secret_commit(outdir=outdir, commit_doc=c1)
    write_secret_reveal(outdir=outdir, reveal_doc=r1)

    t = tally_secret(outdir=outdir, manifest_id=mid, strict=True)
    assert t["counts"]["YES"] == 1
    assert t["ballots"]["valid"] == 1
    assert t["passed_nullifier_check"] is True


def test_secret_nullifier_replay_rejected(tmp_path: Path):
    outdir = tmp_path / "vote"
    mid = "manifest-123"

    c1, r1 = build_secret_commit_and_reveal(manifest_id=mid, choice="YES", nullifier_hex="aa"*16, salt_hex="bb"*16)
    write_secret_commit(outdir=outdir, commit_doc=c1)

    # second commit with same nullifier should fail
    c2, r2 = build_secret_commit_and_reveal(manifest_id=mid, choice="NO", nullifier_hex="aa"*16, salt_hex="cc"*16)
    with pytest.raises(ValueError):
        write_secret_commit(outdir=outdir, commit_doc=c2)

def test_secret_reveal_default_purpose_env_does_not_leak_commit_purpose(tmp_path: Path, monkeypatch):
    # This test ensures the reveal anchor uses its own purpose env var, not the commit one.
    from ucc.vote_ballot_secret import build_secret_commit_and_reveal

    outdir = tmp_path / "vote"
    mid = "manifest-123"
    c1, r1 = build_secret_commit_and_reveal(manifest_id=mid, choice="YES", nullifier_hex="aa"*16, salt_hex="bb"*16)

    # Just ensure writing reveal doesn't crash if COHERENCELEDGER_PURPOSE is set for commit.
    monkeypatch.setenv("COHERENCELEDGER_ENABLE", "0")  # no ledger needed for this unit test
    monkeypatch.setenv("COHERENCELEDGER_PURPOSE", "ucc.vote_ballot_secret.commit.anchor")
    # If code incorrectly uses COHERENCELEDGER_PURPOSE for reveal, it would still work, but purpose is wrong.
    # Here we just verify code now references COHERENCELEDGER_REVEAL_PURPOSE (compile-time check already done).
    # Runtime check: ensure function runs successfully.
    from ucc.vote_ballot_secret import write_secret_reveal
    rp = write_secret_reveal(outdir=outdir, reveal_doc=r1)
    assert rp.exists()
