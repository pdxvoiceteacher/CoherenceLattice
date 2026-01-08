from __future__ import annotations
import json
from pathlib import Path

reg = Path("ucc/verifiers/registry.json")
r = json.loads(reg.read_text(encoding="utf-8-sig"))

for vid in ["stub.sha256.v1", "stub.sha256.pinned.v1"]:
    if vid in r:
        r[vid]["circuit_id"] = "vote_proof_envelope.v1"
        r[vid]["circuit_required"] = True

reg.write_text(json.dumps(r, indent=2, sort_keys=True), encoding="utf-8")
print("Updated verifier registry with circuit_id mapping.")
