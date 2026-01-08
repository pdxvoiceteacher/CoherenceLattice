from __future__ import annotations
from pathlib import Path
import re

fp = Path("ucc/src/ucc/proof_verifiers.py")
txt = fp.read_text(encoding="utf-8")

if "from ucc.snark_backend import get_backend_from_env" not in txt:
    txt = txt.replace(
        "from ucc.verifier_registry import DEFAULT_VERIFIER_ID, get_spec, load_registry, resolve_vk_path",
        "from ucc.verifier_registry import DEFAULT_VERIFIER_ID, get_spec, load_registry, resolve_vk_path\nfrom ucc.snark_backend import get_backend_from_env"
    )

# Replace Groth16/Plonk adapter bodies to call backend
txt = re.sub(
    r"class Groth16VerifierAdapter:.*?class PlonkVerifierAdapter:",
    """class Groth16VerifierAdapter:
    def verify(self, proof_b64: str, public_signals: Dict[str, Any], vk_bytes: Optional[bytes]) -> None:
        if vk_bytes is None:
            raise ValueError("Groth16 verifier requires vk_bytes")
        backend = get_backend_from_env()
        backend.verify(alg="GROTH16", proof_b64=proof_b64, public_signals=public_signals, vk_bytes=vk_bytes)


class PlonkVerifierAdapter:
""",
    txt,
    flags=re.S
)

txt = re.sub(
    r"class PlonkVerifierAdapter:.*?def load_vk_bytes",
    """class PlonkVerifierAdapter:
    def verify(self, proof_b64: str, public_signals: Dict[str, Any], vk_bytes: Optional[bytes]) -> None:
        if vk_bytes is None:
            raise ValueError("PLONK verifier requires vk_bytes")
        backend = get_backend_from_env()
        backend.verify(alg="PLONK", proof_b64=proof_b64, public_signals=public_signals, vk_bytes=vk_bytes)


def load_vk_bytes""",
    txt,
    flags=re.S
)

fp.write_text(txt, encoding="utf-8")
print("Wired Groth16/PLONK adapters to backend (disabled by default).")
