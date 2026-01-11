from __future__ import annotations

"""
Proof Verifiers v0.9

- Loads verifier spec from registry (committed + overlay)
- Loads VK bytes from vk_path and validates vk_sha256 (registry pin)
- Enforces proof-doc vk_sha256 pin when pin_required
- Dispatches to a Verifier implementation:
    - StubSHA256Verifier (current)
    - future: Groth16/Plonk/etc.

This is the stable interface layer that ZK verifiers plug into.
"""

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Optional, Protocol
import base64
import hashlib

from ucc.verifier_registry import DEFAULT_VERIFIER_ID, get_spec, load_registry, resolve_vk_path
from ucc.public_signal_schemas import validate_public_signals
from ucc.circuit_registry import load_and_pin_circuit_descriptor
from ucc.snark_backend import get_backend_from_env


def sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def proof_stub_b64(public_signals: Dict[str, Any]) -> str:
    """
    Deterministic placeholder proof (same as v0.5): base64(sha256("proof_stub|" + joined public signals))
    """
    order = ["manifest_id","ballot_id","nullifier_sha256","ciphertext_sha256","aad_sha256","choice_hash"]
    s = "|".join(f"{k}={public_signals.get(k,'')}" for k in order).encode("utf-8")
    digest = hashlib.sha256(b"proof_stub|" + s).digest()
    return base64.b64encode(digest).decode("ascii")


class Verifier(Protocol):
    def verify(self, proof_b64: str, public_signals: Dict[str, Any], vk_bytes: Optional[bytes]) -> None:
        ...


class StubSHA256Verifier:
    """
    v0.9 stub verifier: checks proof_b64 equals deterministic stub hash of public_signals.
    """
    def verify(self, proof_b64: str, public_signals: Dict[str, Any], vk_bytes: Optional[bytes]) -> None:
        expected = proof_stub_b64(public_signals)
        if proof_b64 != expected:
            raise ValueError("invalid stub proof (proof_b64 does not match public_signals)")


def load_vk_bytes(spec: Dict[str, Any]) -> Optional[bytes]:
    """
    Loads VK bytes from spec["vk_path"] (if present), and validates sha256 matches spec["vk_sha256"] (if present).
    Supports absolute vk_path or repo-relative vk_path.
    """
    vk_path = resolve_vk_path(spec)
    if not vk_path:
        return None
    if not vk_path.exists():
        raise FileNotFoundError(f"vk_path does not exist: {vk_path}")
    b = vk_path.read_bytes()
    expected = spec.get("vk_sha256")
    if expected:
        actual = sha256_hex(b)
        if str(actual) != str(expected):
            raise ValueError("vk_sha256 mismatch for vk file (registry pin violated)")
    return b


def get_verifier_instance(spec: Dict[str, Any]) -> Verifier:
    kind = spec.get("kind")
    if kind == "stub":
        return StubSHA256Verifier()
    raise NotImplementedError(f"Verifier kind not implemented: {kind}")


def verify_envelope(doc: Dict[str, Any], registry: Optional[Dict[str, Dict[str, Any]]] = None) -> None:
    """
    v0.9 canonical envelope verification:
      - schema + required fields
      - select verifier by verifier_id
      - enforce vk pin if required
      - load vk bytes + enforce registry file hash pin
      - run verifier.verify()
    """
    if doc.get("schema_id") != "ucc.vote_proof_envelope.v0_5":
        raise ValueError("wrong schema_id for proof envelope")

    public_signals = doc.get("public_signals")
    if not isinstance(public_signals, dict):
        raise ValueError("public_signals missing")

    proof_b64 = doc.get("proof_b64")
    if not isinstance(proof_b64, str) or not proof_b64:
        raise ValueError("proof_b64 missing")

    reg = registry or load_registry()
    verifier_id = str(doc.get("verifier_id", DEFAULT_VERIFIER_ID))
    spec = get_spec(verifier_id, reg)
    validate_public_signals(public_signals, spec)

    # v1.6: circuit pinning enforcement (verifier -> circuit_id -> circuit_sha256)
    if spec.get("circuit_required", False):
        expected_cid = spec.get("circuit_id")
        got_cid = doc.get("circuit_id")
        if not expected_cid or not got_cid or str(got_cid) != str(expected_cid):
            raise ValueError("circuit_id mismatch (verifier/circuit substitution risk)")

        cinfo = load_and_pin_circuit_descriptor(str(expected_cid))
        expected_sha = cinfo["sha256"]
        got_sha = doc.get("circuit_sha256")
        if not got_sha or str(got_sha) != str(expected_sha):
            raise ValueError("circuit_sha256 mismatch (circuit substitution risk)")

    # Pinning: if required, proof doc must carry the same vk_sha256 as registry
    if spec.get("pin_required", False):
        expected_vk = spec.get("vk_sha256")
        got_vk = doc.get("vk_sha256")
        if not expected_vk or not got_vk or str(got_vk) != str(expected_vk):
            raise ValueError("vk_sha256 pin mismatch (verifier substitution risk)")

    vk_bytes = load_vk_bytes(spec)

    # If pin_required, VK must exist (ensures substitution defense is actually anchored to a real VK)
    if spec.get("pin_required", False) and vk_bytes is None:
        raise ValueError("pin_required verifier requires vk_path + vk_sha256")

    verifier = get_verifier_instance(spec)
    verifier.verify(proof_b64=proof_b64, public_signals=public_signals, vk_bytes=vk_bytes)
