import json
import pytest

from ucc.circuit_registry import load_and_pin_circuit_descriptor
from ucc.vote_ballot_aead import build_aead_commit_and_reveal
from ucc.vote_proof_envelope import build_proof_envelope_from_commit_and_reveal, verify_proof_envelope


def test_circuit_descriptor_pin_loads():
    info = load_and_pin_circuit_descriptor("vote_proof_envelope.v1")
    assert "sha256" in info
    assert info["descriptor"]["name"] == "vote_proof_envelope_v1"


def test_proof_envelope_carries_circuit_pin():
    commit, reveal = build_aead_commit_and_reveal(manifest_id="m", plaintext_choice="YES", nullifier_hex="aa"*16)
    proof = build_proof_envelope_from_commit_and_reveal(commit, reveal, verifier_id="stub.sha256.v1")
    assert proof.get("circuit_id") == "vote_proof_envelope.v1"
    assert isinstance(proof.get("circuit_sha256"), str) and len(proof["circuit_sha256"]) == 64


def test_circuit_pin_tamper_rejected():
    commit, reveal = build_aead_commit_and_reveal(manifest_id="m", plaintext_choice="YES", nullifier_hex="aa"*16)
    proof = build_proof_envelope_from_commit_and_reveal(commit, reveal, verifier_id="stub.sha256.v1")

    proof2 = dict(proof)
    proof2["circuit_sha256"] = "deadbeef"
    with pytest.raises(ValueError):
        verify_proof_envelope(proof2)
