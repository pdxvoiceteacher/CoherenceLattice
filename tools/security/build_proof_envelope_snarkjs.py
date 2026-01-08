from __future__ import annotations
import json
from pathlib import Path

from ucc.proof_formats import wrap_proof, b64_encode_json
from ucc.public_inputs import build_public_inputs_spec, DEFAULT_ORDER
from ucc.verifier_registry import load_registry, get_spec
from ucc.circuit_registry import load_and_pin_circuit_descriptor
from ucc.snark_public_outputs import public_signals_from_public_json


def main() -> int:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--vote-dir", required=True)
    ap.add_argument("--commit", required=True)
    ap.add_argument("--proof-json", required=True)

    # NEW: optional, otherwise read from prover_manifest.json if present
    ap.add_argument("--public-json", default=None)

    ap.add_argument("--verifier-id", default=None)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    vote_dir = Path(args.vote_dir)
    vote_manifest = json.loads((vote_dir / "vote_manifest.json").read_text(encoding="utf-8-sig"))
    policy = vote_manifest.get("proof_policy") if isinstance(vote_manifest, dict) else None

    verifier_id = args.verifier_id or (policy.get("verifier_id") if isinstance(policy, dict) else None) or "stub.sha256.v1"
    reg = load_registry()
    spec = get_spec(verifier_id, reg)

    commit = json.loads(Path(args.commit).read_text(encoding="utf-8-sig"))
    proof_obj = json.loads(Path(args.proof_json).read_text(encoding="utf-8-sig"))

    # Resolve public.json path + order
    public_json_path = Path(args.public_json) if args.public_json else None
    order = DEFAULT_ORDER

    pm = vote_dir / "prover_manifest.json"
    if pm.exists():
        pm_doc = json.loads(pm.read_text(encoding="utf-8-sig"))
        pi = pm_doc.get("public_inputs") if isinstance(pm_doc, dict) else None
        if isinstance(pi, dict) and isinstance(pi.get("order"), list):
            order = [str(x) for x in pi["order"]]
        arts = pm_doc.get("artifacts") if isinstance(pm_doc, dict) else None
        if public_json_path is None and isinstance(arts, dict) and isinstance(arts.get("public_json_path"), str):
            p = arts["public_json_path"]
            public_json_path = (vote_dir / p) if not Path(p).is_absolute() else Path(p)

    if public_json_path is None:
        raise SystemExit("public.json path not provided and prover_manifest.json missing/does not specify artifacts.public_json_path")

    pub_map = public_signals_from_public_json(public_json_path, order)

    # circuit pin
    circuit_id = spec.get("circuit_id")
    c_sha = None
    if circuit_id:
        cinfo = load_and_pin_circuit_descriptor(str(circuit_id))
        c_sha = cinfo["sha256"]

    # Build public_signals primarily from commit/manifest, but choice_hash from public.json
    expected = {
        "manifest_id": str(vote_manifest.get("manifest_id")),
        "ballot_id": str(commit.get("ballot_id")),
        "nullifier_sha256": str(commit.get("nullifier_sha256")),
        "ciphertext_sha256": str(commit.get("ciphertext_sha256")),
        "aad_sha256": str(commit.get("aad_sha256")),
    }

    # cross-check public.json agrees with expected fields (best practice)
    for k, v in expected.items():
        if k in pub_map and str(pub_map[k]) != str(v):
            raise SystemExit(f"public.json mismatch for {k}: expected {v} got {pub_map[k]}")

    choice_hash = pub_map.get("choice_hash")
    if not choice_hash:
        raise SystemExit("public.json does not contain choice_hash at the expected position/order")

    public_signals = dict(expected)
    public_signals["choice_hash"] = str(choice_hash)
    public_signals["public_inputs"] = build_public_inputs_spec(public_signals)

    fmt = "snarkjs.groth16.v1" if str(spec.get("alg","")).upper() == "GROTH16" else "snarkjs.plonk.v1"
    proof_b64 = b64_encode_json(wrap_proof(fmt, proof_obj))

    envelope = {
        "schema_id": "ucc.vote_proof_envelope.v0_5",
        "version": 5,
        "created_at": __import__("datetime").datetime.utcnow().replace(microsecond=0).isoformat() + "Z",
        "verifier_id": verifier_id,
        "vk_sha256": spec.get("vk_sha256"),
        "circuit_id": circuit_id,
        "circuit_sha256": c_sha,
        "proof_alg": spec.get("alg"),
        "public_signals": public_signals,
        "proof_b64": proof_b64,
    }

    out = Path(args.out) if args.out else (vote_dir / "secret_v03" / "proofs" / f"proof_{public_signals['ballot_id']}.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(envelope, indent=2, sort_keys=True), encoding="utf-8", newline="\n")

    print(f"Wrote: {out}")
    print(f"choice_hash(from public.json)={choice_hash}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
