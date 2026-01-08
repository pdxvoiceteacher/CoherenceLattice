from __future__ import annotations
from pathlib import Path
import re

fp = Path("ucc/src/ucc/vote_proof_envelope.py")
txt = fp.read_text(encoding="utf-8")

# Ensure import
if "from ucc.public_inputs import build_public_inputs_spec" not in txt:
    txt = txt.replace(
        "from ucc.proof_verifiers import proof_stub_b64, verify_envelope",
        "from ucc.proof_verifiers import proof_stub_b64, verify_envelope\nfrom ucc.public_inputs import build_public_inputs_spec"
    )

# Insert public_inputs spec once, right after the first public_signals dict literal
marker = "public_signals[\"public_inputs\"] = build_public_inputs_spec(public_signals)"
if marker not in txt:
    txt = re.sub(
        r"(public_signals = \{.*?\n\s*\}\n)",
        r"\1\n    # v1.4: embed versioned snarkjs public input vector\n    public_signals[\"public_inputs\"] = build_public_inputs_spec(public_signals)\n",
        txt,
        count=1,
        flags=re.S
    )

fp.write_text(txt, encoding="utf-8")
print("Patched vote_proof_envelope.py to embed public_inputs spec.")
