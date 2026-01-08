from __future__ import annotations
from pathlib import Path
import re

fp = Path("ucc/src/ucc/snark_backend.py")
txt = fp.read_text(encoding="utf-8")

# Ensure import
if "from ucc.public_inputs import to_snarkjs_public_inputs" not in txt:
    txt = txt.replace("import tempfile", "import tempfile\n\nfrom ucc.public_inputs import to_snarkjs_public_inputs")

# Replace the _public_inputs_for_snarkjs function by a simple call site
# (We don't need to delete the old function; but we remove usage.)
txt = re.sub(r"public_inputs = _public_inputs_for_snarkjs\(public_signals\)",
             "strict_inputs = _truthy(os.getenv('UCC_SNARK_STRICT_PUBLIC_INPUTS','1'))\n        public_inputs = to_snarkjs_public_inputs(public_signals, strict=strict_inputs)",
             txt)

fp.write_text(txt, encoding="utf-8")
print("Patched snark_backend.py to use public_inputs adapter.")
