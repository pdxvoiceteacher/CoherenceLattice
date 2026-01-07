from pathlib import Path
import pytest

from ucc.vote_ballot_aead import build_aead_commit_and_reveal, write_aead_commit, write_aead_reveal
from ucc.vote_tally_aead import tally_aead


def test_aead_commit_reveal_tally_no_plaintext(tmp_path: Path):
    outdir = tmp_path / "vote"
    mid = "manifest-aead"

    c, r = build_aead_commit_and_reveal(manifest_id=mid, plaintext_choice="YES", nullifier_hex="aa"*16)
    # reveal must not contain plaintext_choice in v0.4
    assert "plaintext_choice" not in r

    write_aead_commit(outdir=outdir, commit_doc=c)
    write_aead_reveal(outdir=outdir, reveal_doc=r)

    t = tally_aead(outdir=outdir, manifest_id=mid, strict=True)
    assert t["counts"]["YES"] == 1
    assert t["ballots"]["valid"] == 1


def test_aead_nullifier_replay_rejected(tmp_path: Path):
    outdir = tmp_path / "vote"
    mid = "manifest-aead"

    c1, _ = build_aead_commit_and_reveal(manifest_id=mid, plaintext_choice="YES", nullifier_hex="aa"*16)
    write_aead_commit(outdir=outdir, commit_doc=c1)

    c2, _ = build_aead_commit_and_reveal(manifest_id=mid, plaintext_choice="NO", nullifier_hex="aa"*16)
    with pytest.raises(ValueError):
        write_aead_commit(outdir=outdir, commit_doc=c2)
