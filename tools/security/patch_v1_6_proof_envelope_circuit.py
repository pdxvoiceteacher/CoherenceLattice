from __future__ import annotations
from pathlib import Path
import re

fp = Path("ucc/src/ucc/vote_proof_envelope.py")
txt = fp.read_text(encoding="utf-8")

# Ensure import
if "from ucc.circuit_registry import load_and_pin_circuit_descriptor" not in txt:
    txt = txt.replace(
        "from ucc.proof_verifiers import proof_stub_b64, verify_envelope",
        "from ucc.proof_verifiers import proof_stub_b64, verify_envelope\nfrom ucc.circuit_registry import load_and_pin_circuit_descriptor"
    )

# Insert circuit pin into proof doc creation (right before return dict)
needle = '"vk_sha256": spec.get("vk_sha256"),'
if needle in txt and '"circuit_id"' not in txt:
    txt = txt.replace(
        needle,
        needle + '\n        "circuit_id": spec.get("circuit_id"),\n        "circuit_sha256": None,'
    )

# After the proof dict is created, we set circuit_sha256 if circuit_id exists
# Add a small block right before return { ... } by hooking after spec is loaded
if "load_and_pin_circuit_descriptor" in txt and "circuit_sha256" in txt and "cinfo =" not in txt:
    txt = txt.replace(
        "spec = get_spec(verifier_id, registry)",
        "spec = get_spec(verifier_id, registry)\n\n    # v1.6: circuit pinning (verifier_id -> circuit_id -> circuit_sha256)\n    c_id = spec.get('circuit_id')\n    c_sha = None\n    if c_id:\n        cinfo = load_and_pin_circuit_descriptor(str(c_id))\n        c_sha = cinfo['sha256']\n"
    )
    # Set circuit_sha256 in returned dict by replacing the placeholder None
    txt = txt.replace('"circuit_sha256": None,', '"circuit_sha256": c_sha,', 1)

fp.write_text(txt, encoding="utf-8")
print("Patched vote_proof_envelope.py to include circuit_id + circuit_sha256.")
