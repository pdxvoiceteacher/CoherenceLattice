from __future__ import annotations
from pathlib import Path

fp = Path("ucc/src/ucc/proof_verifiers.py")
txt = fp.read_text(encoding="utf-8")

if "from ucc.circuit_registry import load_and_pin_circuit_descriptor" not in txt:
    txt = txt.replace(
        "from ucc.public_signal_schemas import validate_public_signals",
        "from ucc.public_signal_schemas import validate_public_signals\nfrom ucc.circuit_registry import load_and_pin_circuit_descriptor"
    )

needle = "validate_public_signals(public_signals, spec)\n"
if needle in txt and "circuit_id" not in txt.split(needle,1)[1][:400]:
    insert = """validate_public_signals(public_signals, spec)

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
"""
    txt = txt.replace(needle, insert)

fp.write_text(txt, encoding="utf-8")
print("Patched proof_verifiers.verify_envelope with circuit pinning checks.")
