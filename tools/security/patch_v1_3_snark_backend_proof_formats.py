from __future__ import annotations
from pathlib import Path
import re

fp = Path("ucc/src/ucc/snark_backend.py")
txt = fp.read_text(encoding="utf-8")

# Ensure import
if "from ucc.proof_formats import to_snarkjs_proof" not in txt:
    txt = txt.replace("import tempfile", "import tempfile\n\nfrom ucc.proof_formats import to_snarkjs_proof")

# Remove the old _decode_proof_json function if present (best-effort)
txt = re.sub(r"def _decode_proof_json\(proof_b64: str\).*?\n\n", "", txt, flags=re.S)

# Replace proof_obj assignment
txt = txt.replace(
    "proof_obj = _decode_proof_json(proof_b64)",
    "proof_obj = to_snarkjs_proof(proof_b64, expected_alg=alg_u)"
)

fp.write_text(txt, encoding="utf-8")
print("Patched snark_backend.py to use proof_formats adapters.")
