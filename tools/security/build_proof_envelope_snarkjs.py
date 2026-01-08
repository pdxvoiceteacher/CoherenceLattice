from __future__ import annotations
import json
import os
from pathlib import Path

from ucc.proof_formats import wrap_proof, b64_encode_json
from ucc.public_inputs import build_public_inputs_spec, DEFAULT_ORDER
from ucc.verifier_registry import load_registry, get_spec
from ucc.circuit_registry import load_and_pin_circuit_descriptor
from ucc.snark_public_outputs import public_signals_from_public_json
from ucc.public_signal_schemas import validate_public_signals


def truthy(s: str) -> bool:
    return s.strip().lower() in {"1","true","yes","y","on"}


def main() -> int:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--vote-dir", required=True)
    ap.add_argument("--commit", required=True)
    ap.add_argument("--proof-json", required=True)
    ap.add_argument("--public-json", default=None)   # optional; else from prover_manifest.json
    ap.add_argument("--verifier-id", default=None)   # v2.4: refused for strict public.deliberation
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    vote_dir = Path(args.vote_dir)

    vote_manifest = json.loads((vote_dir / "vote_manifest.json").read_text(encoding="utf-8-sig"))
    purpose = vote_manifest.get("purpose") if isinstance(vote_manifest, dict) else {}
    scope = (purpose.get("scope") if isinstance(purpose, dict) else None) or ""
    policy = vote_manifest.get("proof_policy") if isinstance(vote_manifest, dict) else None

    # Resolve strict mode + order/public.json path from prover_manifest.json
    public_json_path = Path(args.public_json) if args.public_json else None
    order = list(DEFAULT_ORDER)
    strict_mode = truthy(os.getenv("COHERENCELEDGER_STRICT", "0"))

    pm = vote_dir / "prover_manifest.json"
    if pm.exists():
        pm_doc = json.loads(pm.read_text(encoding="utf-8-sig"))
        pi = pm_doc.get("public_inputs") if isinstance(pm_doc, dict) else None
        if isinstance(pi, dict):
            if isinstance(pi.get("order"), list):
                order = [str(x) for x in pi["order"]]
            if isinstance(pi.get("strict"), bool):
                strict_mode = bool(pi["strict"])
        arts = pm_doc.get("artifacts") if isinstance(pm_doc, dict) else None
        if public_json_path is None and isinstance(arts, dict) and isinstance(arts.get("public_json_path"), str):
            p = arts["public_json_path"]
            public_json_path = (vote_dir / p) if not Path(p).is_absolute() else Path(p)

    if public_json_path is None:
        raise SystemExit("public.json not provided and prover_manifest.json missing/does not specify artifacts.public_json_path")

    if "public_inputs" in order:
        raise SystemExit("public_inputs must not appear in public input order (it is derived/embedded separately)")

    # v2.4 strict scope: refuse override + require manifest proof_policy
    is_public_strict = bool(strict_mode and scope == "public.deliberation")

    policy_verifier = None
    policy_circuit = None
    if isinstance(policy, dict):
        if isinstance(policy.get("verifier_id"), str):
            policy_verifier = policy["verifier_id"]
        if isinstance(policy.get("circuit_id"), str):
            policy_circuit = policy["circuit_id"]

    if is_public_strict:
        if args.verifier_id is not None:
            raise SystemExit("Overrides disabled in strict public.deliberation; remove --verifier-id")
        if not policy_verifier or not policy_circuit:
            raise SystemExit("public.deliberation strict requires vote_manifest.proof_policy {verifier_id,circuit_id}")

    # Choose verifier_id: prefer manifest policy when present
    verifier_id = policy_verifier or args.verifier_id or "stub.sha256.v1"

    reg = load_registry()
    spec = get_spec(verifier_id, reg)

    # Enforce policy circuit mapping (especially important for strict public.deliberation)
    spec_circuit = spec.get("circuit_id")
    if policy_circuit:
        if not spec_circuit:
            raise SystemExit("Verifier spec has no circuit_id but manifest proof_policy requires one")
        if str(spec_circuit) != str(policy_circuit):
            raise SystemExit(f"proof_policy.circuit_id mismatch: manifest={policy_circuit} verifier_spec={spec_circuit}")

    commit = json.loads(Path(args.commit).read_text(encoding="utf-8-sig"))
    proof_obj = json.loads(Path(args.proof_json).read_text(encoding="utf-8-sig"))

    # Load pinned circuit descriptor (if any) to enforce strict order
    circuit_id = policy_circuit or spec_circuit
    c_sha = None
    expected_order = list(DEFAULT_ORDER)

    if circuit_id:
        cinfo = load_and_pin_circuit_descriptor(str(circuit_id))
        c_sha = cinfo["sha256"]
        desc = cinfo.get("descriptor", {})
        constraints = desc.get("constraints", {}) if isinstance(desc, dict) else {}
        po = constraints.get("public_inputs_order")
        if isinstance(po, list) and all(isinstance(x, str) for x in po):
            expected_order = list(po)

    if strict_mode:
        if order != expected_order:
            raise SystemExit(f"STRICT order mismatch: got={order} expected={expected_order}")

    # v2.2: derive ALL public signals from public.json
    pub_map = public_signals_from_public_json(public_json_path, order)

    # Cross-check commit/manifest (sanity checks only)
    manifest_id_expected = str(vote_manifest.get("manifest_id"))
    if "manifest_id" in pub_map and str(pub_map["manifest_id"]) != manifest_id_expected:
        raise SystemExit(f"public.json mismatch manifest_id: expected {manifest_id_expected} got {pub_map['manifest_id']}")

    for k in ("ballot_id","nullifier_sha256","ciphertext_sha256","aad_sha256"):
        if k in commit and k in pub_map and str(commit[k]) != str(pub_map[k]):
            raise SystemExit(f"public.json mismatch {k}: commit={commit[k]} public={pub_map[k]}")

    public_signals = {k: str(pub_map[k]) for k in order}
    public_signals["public_inputs"] = build_public_inputs_spec(public_signals, order=order)

    # v2.3: schema enforcement BEFORE writing
    validate_public_signals(public_signals, spec)

    alg = str(spec.get("alg","")).upper()
    if alg == "GROTH16":
        fmt = "snarkjs.groth16.v1"
    elif alg == "PLONK":
        fmt = "snarkjs.plonk.v1"
    else:
        raise SystemExit(f"Verifier alg must be GROTH16/PLONK for snarkjs boundary, got: {alg}")

    proof_b64 = b64_encode_json(wrap_proof(fmt, proof_obj))

    envelope = {
        "schema_id": "ucc.vote_proof_envelope.v0_5",
        "version": 8,
        "created_at": __import__("datetime").datetime.utcnow().replace(microsecond=0).isoformat() + "Z",
        "verifier_id": verifier_id,
        "vk_sha256": spec.get("vk_sha256"),
        "circuit_id": circuit_id,
        "circuit_sha256": c_sha,
        "proof_alg": spec.get("alg"),
        "public_signals": public_signals,
        "proof_b64": proof_b64,
    }

    ballot_id = public_signals.get("ballot_id", "unknown")
    out = Path(args.out) if args.out else (vote_dir / "secret_v03" / "proofs" / f"proof_{ballot_id}.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(envelope, indent=2, sort_keys=True), encoding="utf-8", newline="\n")

    print(f"Wrote: {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
