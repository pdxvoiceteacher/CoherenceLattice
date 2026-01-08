from __future__ import annotations
import json
from pathlib import Path

from ucc.proof_formats import wrap_proof, b64_encode_json
from ucc.public_inputs import build_public_inputs_spec
from ucc.verifier_registry import load_registry, get_spec
from ucc.circuit_registry import load_and_pin_circuit_descriptor


def main() -> int:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--vote-dir", required=True)
    ap.add_argument("--commit", required=True)
    ap.add_argument("--proof-json", required=True)
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

    circuit_id = spec.get("circuit_id")
    c_sha = None
    if circuit_id:
        cinfo = load_and_pin_circuit_descriptor(str(circuit_id))
        c_sha = cinfo["sha256"]

    # Public signals must already include choice_hash in your workflow; v2.1 can read it from public.json instead.
    choice_hash = str(commit.get("choice_hash", ""))
    if not choice_hash:
        raise SystemExit("Missing choice_hash in commit. (Add it or extend builder to read from public.json.)")

    public_signals = {
        "manifest_id": str(vote_manifest.get("manifest_id")),
        "ballot_id": str(commit.get("ballot_id")),
        "nullifier_sha256": str(commit.get("nullifier_sha256")),
        "ciphertext_sha256": str(commit.get("ciphertext_sha256")),
        "aad_sha256": str(commit.get("aad_sha256")),
        "choice_hash": choice_hash,
    }
    public_signals["public_inputs"] = build_public_inputs_spec(public_signals)

    fmt = "snarkjs.groth16.v1" if str(spec.get("alg","")).upper() == "GROTH16" else "snarkjs.plonk.v1"
    proof_b64 = b64_encode_json(wrap_proof(fmt, proof_obj))

    envelope = {
        "schema_id": "ucc.vote_proof_envelope.v0_5",
        "version": 4,
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
