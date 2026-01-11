from __future__ import annotations

from typing import Any, Dict, List

from ucc.verifier_registry import load_registry, get_spec
from ucc.circuit_registry import load_and_pin_circuit_descriptor


PUBLIC_SCOPE_REQUIRED = {
    "verifier_id": "stub.sha256.public.pinned.v1",
    "circuit_id": "vote_proof_envelope_public.v1",
}


def scope_policy_violations(manifest: Dict[str, Any], *, strict: bool) -> List[Dict[str, str]]:
    """
    Returns list of violations for scope-bound proof/circuit policy.
    Only enforced in strict mode for public.deliberation.
    """
    v: List[Dict[str, str]] = []
    purpose = manifest.get("purpose") or {}
    scope = purpose.get("scope")

    if not (strict and scope == "public.deliberation"):
        return v

    pp = manifest.get("proof_policy")
    if not isinstance(pp, dict):
        v.append({"code":"proof_policy", "path":"proof_policy", "message":"public.deliberation requires proof_policy object in strict mode"})
        return v

    verifier_id = pp.get("verifier_id")
    circuit_id = pp.get("circuit_id")
    if verifier_id != PUBLIC_SCOPE_REQUIRED["verifier_id"]:
        v.append({"code":"proof_policy.verifier_id", "path":"proof_policy.verifier_id", "message":f"public.deliberation requires verifier_id={PUBLIC_SCOPE_REQUIRED['verifier_id']}"})
    if circuit_id != PUBLIC_SCOPE_REQUIRED["circuit_id"]:
        v.append({"code":"proof_policy.circuit_id", "path":"proof_policy.circuit_id", "message":f"public.deliberation requires circuit_id={PUBLIC_SCOPE_REQUIRED['circuit_id']}"})

    # If basic fields are correct, validate registry mappings + pins
    if verifier_id == PUBLIC_SCOPE_REQUIRED["verifier_id"]:
        try:
            reg = load_registry()
            spec = get_spec(verifier_id, reg)
            if spec.get("circuit_id") != circuit_id:
                v.append({"code":"verifier.circuit_id", "path":"proof_policy", "message":"verifier registry circuit_id does not match manifest proof_policy.circuit_id"})
        except Exception as e:
            v.append({"code":"verifier.registry", "path":"proof_policy.verifier_id", "message":f"verifier registry check failed: {e}"})

    if circuit_id == PUBLIC_SCOPE_REQUIRED["circuit_id"]:
        try:
            load_and_pin_circuit_descriptor(circuit_id)  # ensures circuit pin is valid
        except Exception as e:
            v.append({"code":"circuit.pin", "path":"proof_policy.circuit_id", "message":f"circuit pin check failed: {e}"})

    return v
