import json
import hashlib
import os
import subprocess
import sys
from pathlib import Path


def _sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def test_strict_public_uses_manifest_output_path(tmp_path: Path):
    repo_root = Path(__file__).resolve().parents[2]
    script = (repo_root / "tools" / "security" / "build_proof_envelope_snarkjs.py").resolve()

    vote = tmp_path / "vote"
    (vote / "secret_v03" / "commits").mkdir(parents=True)
    (vote / "secret_v03" / "proofs").mkdir(parents=True)

    nullifier = "a" * 64
    cts = "b" * 64
    aad = "c" * 64
    ch = "d" * 64
    manifest_id = "m"
    ballot_id = "b"

    schema_path = repo_root / "ucc" / "schemas" / "public_signals" / "vote_proof_envelope_public_signals_v1.schema.json"
    schema_sha = _sha256(schema_path)

    vk = tmp_path / "vk.json"
    vk.write_text('{"vk":"dummy"}', encoding="utf-8")
    vk_sha = _sha256(vk)

    reg = tmp_path / "reg.json"
    reg.write_text(json.dumps({
        "test.public.groth16": {
            "kind":"snark",
            "alg":"GROTH16",
            "enabled": True,
            "vk_path": str(vk),
            "vk_sha256": vk_sha,
            "pin_required": False,
            "signals_schema_path": str(schema_path),
            "signals_schema_sha256": schema_sha,
            "signals_schema_required": True,
            "circuit_id": "vote_proof_envelope_public.v1",
            "circuit_required": True
        }
    }, indent=2), encoding="utf-8")

    (vote / "vote_manifest.json").write_text(json.dumps({
        "manifest_id": manifest_id,
        "purpose": {"scope":"public.deliberation"},
        "proof_policy": {"verifier_id":"test.public.groth16", "circuit_id":"vote_proof_envelope_public.v1"}
    }), encoding="utf-8")

    out_rel = "secret_v03/proofs/manifest_bound.json"
    out_path = vote / "secret_v03" / "proofs" / "manifest_bound.json"

    (vote / "prover_manifest.json").write_text(json.dumps({
        "schema_id":"ucc.prover_manifest.v2",
        "version":2,
        "vote_dir": str(vote),
        "verifier_id":"test.public.groth16",
        "circuit_id":"vote_proof_envelope_public.v1",
        "backend":{"name":"snarkjs","alg":"GROTH16","mode":"fullprover"},
        "artifacts":{"vk_path": str(vk), "proof_json_path":"proof.json", "public_json_path":"public.json"},
        "outputs":{"proof_envelope_path": out_rel},
        "public_inputs":{"format":"snarkjs.public_inputs.v1","version":1,"order":["manifest_id","ballot_id","nullifier_sha256","ciphertext_sha256","aad_sha256","choice_hash"],"strict": True}
    }), encoding="utf-8")

    (vote / "secret_v03" / "commits" / "commit_b.json").write_text(json.dumps({
        "ballot_id": ballot_id,
        "nullifier_sha256": nullifier,
        "ciphertext_sha256": cts,
        "aad_sha256": aad
    }), encoding="utf-8")

    (vote / "proof.json").write_text(json.dumps({"pi_a":[1,2],"pi_b":[[1,2],[3,4]],"pi_c":[5,6]}), encoding="utf-8")
    (vote / "public.json").write_text(json.dumps([manifest_id, ballot_id, nullifier, cts, aad, ch]), encoding="utf-8")

    env = dict(os.environ)
    env["UCC_VERIFIER_REGISTRY_PATH"] = str(reg)

    r = subprocess.run(
        [sys.executable, str(script),
         "--vote-dir", str(vote),
         "--commit", str(vote/"secret_v03/commits/commit_b.json"),
         "--proof-json", str(vote/"proof.json")],
        cwd=str(repo_root),
        env=env,
        capture_output=True,
        text=True
    )

    assert r.returncode == 0, (r.stdout + r.stderr)
    assert out_path.exists()
