from __future__ import annotations
import json, hashlib
from pathlib import Path

reg = Path("ucc/circuits/registry.json")
cir = Path("ucc/circuits/vote_proof_envelope_v1.circuit.json")

r = json.loads(reg.read_text(encoding="utf-8-sig"))
sha = hashlib.sha256(cir.read_bytes()).hexdigest()
r["vote_proof_envelope.v1"]["circuit_sha256"] = sha
reg.write_text(json.dumps(r, indent=2, sort_keys=True), encoding="utf-8")
print("Pinned circuit_sha256:", sha)
