from __future__ import annotations

"""
Proof Format Adapters v1.3

Goals:
- Standardize proof_b64 to be a base64-encoded UTF-8 JSON object with:
    { "format": "...", "version": 1, "data": <backend-specific proof> }
- Validate shape/version early (before subprocess/backends).
- Provide conversion into backend-native objects (snarkjs expects proof JSON object).
"""

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple
import base64
import json


class ProofFormatError(ValueError):
    pass


SUPPORTED_FORMATS = {
    "stub.sha256.v1",
    "snarkjs.groth16.v1",
    "snarkjs.plonk.v1",
}


def b64_encode_json(obj: Any) -> str:
    s = json.dumps(obj, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
    return base64.b64encode(s.encode("utf-8")).decode("ascii")


def b64_decode_json(s: str) -> Any:
    try:
        raw = base64.b64decode(s.encode("ascii"))
    except Exception as e:
        raise ProofFormatError("proof_b64 must be base64") from e
    try:
        txt = raw.decode("utf-8")
    except Exception as e:
        raise ProofFormatError("proof_b64 must decode to UTF-8 JSON") from e
    try:
        return json.loads(txt)
    except Exception as e:
        raise ProofFormatError("proof_b64 must be JSON") from e


def wrap_proof(format_id: str, data: Any, version: int = 1) -> Dict[str, Any]:
    if format_id not in SUPPORTED_FORMATS:
        raise ProofFormatError(f"Unsupported proof format: {format_id}")
    return {"format": format_id, "version": int(version), "data": data}


def unwrap_proof(proof_b64: str) -> Dict[str, Any]:
    obj = b64_decode_json(proof_b64)
    if not isinstance(obj, dict):
        raise ProofFormatError("proof object must be a JSON object")
    fmt = obj.get("format")
    ver = obj.get("version")
    data = obj.get("data")
    if fmt not in SUPPORTED_FORMATS:
        raise ProofFormatError(f"Unsupported proof format: {fmt}")
    if ver != 1:
        raise ProofFormatError(f"Unsupported proof version: {ver}")
    if "data" not in obj:
        raise ProofFormatError("proof object missing 'data'")
    return {"format": fmt, "version": ver, "data": data}


def validate_stub_sha256(data: Any) -> None:
    # stub proofs are just bytes (base64) or short strings; we accept str only
    if not isinstance(data, str) or not data:
        raise ProofFormatError("stub.sha256.v1 data must be a non-empty string")


def validate_snarkjs_groth16(data: Any) -> None:
    """
    snarkjs groth16 proof object typically has:
      pi_a, pi_b, pi_c (and protocol/curve sometimes)
    We'll validate minimum shape: dict with required keys.
    """
    if not isinstance(data, dict):
        raise ProofFormatError("snarkjs.groth16.v1 data must be an object")
    for k in ("pi_a", "pi_b", "pi_c"):
        if k not in data:
            raise ProofFormatError(f"snarkjs.groth16 missing key: {k}")


def validate_snarkjs_plonk(data: Any) -> None:
    """
    snarkjs plonk proof object typically has:
      proof, publicSignals in some contexts; verify expects separate public.json
    We'll validate minimum: dict with 'proof' key.
    """
    if not isinstance(data, dict):
        raise ProofFormatError("snarkjs.plonk.v1 data must be an object")
    if "proof" not in data:
        raise ProofFormatError("snarkjs.plonk missing key: proof")


def validate_proof_object(fmt: str, data: Any) -> None:
    if fmt == "stub.sha256.v1":
        validate_stub_sha256(data)
    elif fmt == "snarkjs.groth16.v1":
        validate_snarkjs_groth16(data)
    elif fmt == "snarkjs.plonk.v1":
        validate_snarkjs_plonk(data)
    else:
        raise ProofFormatError(f"Unhandled proof format: {fmt}")


def to_snarkjs_proof(proof_b64: str, expected_alg: str) -> Dict[str, Any]:
    """
    Returns backend-native snarkjs proof JSON object after validation.

    expected_alg: GROTH16 or PLONK
    """
    u = unwrap_proof(proof_b64)
    fmt = u["format"]
    data = u["data"]

    alg = expected_alg.upper().strip()
    if alg == "GROTH16" and fmt != "snarkjs.groth16.v1":
        raise ProofFormatError(f"Expected snarkjs.groth16.v1 for GROTH16, got {fmt}")
    if alg == "PLONK" and fmt != "snarkjs.plonk.v1":
        raise ProofFormatError(f"Expected snarkjs.plonk.v1 for PLONK, got {fmt}")

    validate_proof_object(fmt, data)
    return data
