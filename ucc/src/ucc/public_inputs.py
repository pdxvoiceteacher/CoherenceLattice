from __future__ import annotations

"""
Public Inputs Adapters v1.4

Goal:
- Provide a stable, versioned representation of the public input vector needed by verifiers (snarkjs).
- Avoid implicit env-only ordering; enforce shape/version when strict.

Spec stored in public_signals["public_inputs"] as an object:
{
  "format": "snarkjs.public_inputs.v1",
  "version": 1,
  "order": ["k1","k2",...],
  "values": ["v1","v2",...]
}

Fallbacks (only if strict=False):
- If public_signals["public_inputs"] is already a list -> use it
- Else if env UCC_SNARK_PUBLIC_SIGNAL_ORDER is set -> build list from dict keys
"""

from typing import Any, Dict, List, Optional
import os


class PublicInputsError(ValueError):
    pass


FORMAT_ID = "snarkjs.public_inputs.v1"
VERSION = 1

# Default order aligns with proof stub / envelope ordering
DEFAULT_ORDER = [
    "manifest_id",
    "ballot_id",
    "nullifier_sha256",
    "ciphertext_sha256",
    "aad_sha256",
    "choice_hash",
]


def _truthy(s: str) -> bool:
    return s.strip().lower() in {"1","true","yes","y","on"}


def build_public_inputs_spec(public_signals: Dict[str, Any], order: Optional[List[str]] = None) -> Dict[str, Any]:
    order = order or DEFAULT_ORDER
    if not isinstance(order, list) or not all(isinstance(k, str) and k for k in order):
        raise PublicInputsError("order must be a list of non-empty strings")

    values: List[str] = []
    for k in order:
        if k not in public_signals:
            raise PublicInputsError(f"public_signals missing key required for public inputs: {k}")
        values.append(str(public_signals[k]))

    return {"format": FORMAT_ID, "version": VERSION, "order": order, "values": values}


def validate_public_inputs_spec(spec: Dict[str, Any]) -> None:
    if not isinstance(spec, dict):
        raise PublicInputsError("public_inputs spec must be an object")
    if spec.get("format") != FORMAT_ID:
        raise PublicInputsError(f"public_inputs.format must be {FORMAT_ID}")
    if spec.get("version") != VERSION:
        raise PublicInputsError(f"public_inputs.version must be {VERSION}")

    order = spec.get("order")
    values = spec.get("values")
    if not isinstance(order, list) or not all(isinstance(k, str) and k for k in order):
        raise PublicInputsError("public_inputs.order must be list[str]")
    if not isinstance(values, list) or not all(isinstance(v, str) for v in values):
        raise PublicInputsError("public_inputs.values must be list[str]")
    if len(order) != len(values):
        raise PublicInputsError("public_inputs.order and values must be same length")


def to_snarkjs_public_inputs(public_signals: Dict[str, Any], strict: bool = True) -> List[Any]:
    """
    Return the snarkjs public input array (JSON array). Typically strings.
    """
    pi = public_signals.get("public_inputs")

    # v1.4 preferred: object spec
    if isinstance(pi, dict):
        validate_public_inputs_spec(pi)
        return list(pi["values"])

    # Legacy list (only if strict=False)
    if isinstance(pi, list):
        if strict:
            raise PublicInputsError("legacy public_inputs list not allowed in strict mode; use v1 spec object")
        return pi

    # Legacy env ordering (only if strict=False)
    order_env = os.getenv("UCC_SNARK_PUBLIC_SIGNAL_ORDER", "").strip()
    if order_env:
        if strict:
            raise PublicInputsError("env-ordered public inputs not allowed in strict mode; embed v1 spec object")
        keys = [k.strip() for k in order_env.split(",") if k.strip()]
        out: List[Any] = []
        for k in keys:
            if k not in public_signals:
                raise PublicInputsError(f"public_signals missing ordered key: {k}")
            out.append(public_signals[k])
        return out

    raise PublicInputsError("No public_inputs spec found (and no legacy fallbacks available)")
