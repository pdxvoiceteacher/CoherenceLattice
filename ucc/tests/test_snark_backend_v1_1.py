import json
import hashlib
from pathlib import Path

import pytest

from ucc.vote_ballot_aead import build_aead_commit_and_reveal
from ucc.vote_proof_envelope import build_proof_envelope_from_commit_and_reveal, verify_proof_envelope


def _write_overlay_registry(path: Path, obj: dict) -> None:
    path.write_text(json.dumps(obj, indent=2), encoding="utf-8")


def test_enabled_groth16_calls_backend_and_is_disabled(tmp_path: Path, monkeypatch):
    vk = tmp_path / "vk.json"
    vk.write_text('{"vk":"one"}', encoding="utf-8")
    sha = hashlib.sha256(vk.read_bytes()).hexdigest()

    reg = tmp_path / "reg.json"
    _write_overlay_registry(reg, {
        "test.groth16": {
            "kind": "snark",
            "alg": "GROTH16",
            "enabled": True,
            "vk_path": str(vk),
            "vk_sha256": sha,
            "pin_required": True
        }
    })
    monkeypatch.setenv("UCC_VERIFIER_REGISTRY_PATH", str(reg))

    commit, reveal = build_aead_commit_and_reveal(manifest_id="m", plaintext_choice="YES", nullifier_hex="aa"*16)
    proof = build_proof_envelope_from_commit_and_reveal(commit, reveal, verifier_id="test.groth16")

    with pytest.raises(NotImplementedError):
        verify_proof_envelope(proof)
