from __future__ import annotations
import json, hashlib
from pathlib import Path

reg_path = Path("ucc/verifiers/registry.json")
vk_path = Path("ucc/verifiers/dummy_vk.json")
sha = hashlib.sha256(vk_path.read_bytes()).hexdigest()

reg = json.loads(reg_path.read_text(encoding="utf-8-sig")) if reg_path.exists() else {}
reg["stub.sha256.pinned.v1"] = {
    "kind": "stub",
    "alg": "PROOF_STUB_SHA256",
    "enabled": True,
    "vk_path": "ucc/verifiers/dummy_vk.json",
    "vk_sha256": sha,
    "pin_required": True
}
# ensure the base stub exists too
reg.setdefault("stub.sha256.v1", {
    "kind": "stub",
    "alg": "PROOF_STUB_SHA256",
    "enabled": True,
    "vk_path": None,
    "vk_sha256": None,
    "pin_required": False
})

reg_path.parent.mkdir(parents=True, exist_ok=True)
reg_path.write_text(json.dumps(reg, indent=2, sort_keys=True), encoding="utf-8")
print("Updated registry with stub.sha256.pinned.v1")
print("vk_sha256 =", sha)
