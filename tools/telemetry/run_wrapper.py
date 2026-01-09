#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, platform, subprocess, sys, statistics
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]

def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def run(cmd: list[str], cwd: Path | None = None) -> None:
    subprocess.run(cmd, cwd=str(cwd) if cwd else None, check=True)

def load_json_bom_safe(p: Path):
    return json.loads(p.read_text(encoding="utf-8-sig"))

def git_commit() -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    except Exception:
        return "unknown"

def run_smoke(smoke_out: Path, quick: bool) -> Path:
    smoke_out.mkdir(parents=True, exist_ok=True)
    run([sys.executable, "python/experiments/konomi_smoke/run_smoke.py",
         "--quick" if quick else "--full", "--outdir", str(smoke_out)], cwd=REPO)
    summary = smoke_out / "konomi_smoke_summary.json"
    if not summary.exists():
        raise SystemExit(f"Missing expected smoke summary: {summary}")
    return summary

def run_ucc(module: str, input_path: Path, outdir: Path) -> tuple[Path, Path]:
    outdir.mkdir(parents=True, exist_ok=True)
    run([sys.executable, "-m", "ucc.cli", "run", module, "--input", str(input_path), "--outdir", str(outdir)], cwd=REPO)
    audit_bundle = outdir / "audit_bundle.json"
    if not audit_bundle.exists():
        raise SystemExit(f"Missing audit_bundle.json at {audit_bundle}")

    snap_out = outdir / "telemetry_snapshot_out"
    snap_out.mkdir(parents=True, exist_ok=True)
    run([sys.executable, "-m", "ucc.cli", "run", "ucc/modules/telemetry_snapshot_v1.yml",
         "--input", str(audit_bundle), "--outdir", str(snap_out)], cwd=REPO)

    snap_json = snap_out / "telemetry_snapshot.json"
    if not snap_json.exists():
        raise SystemExit(f"Missing telemetry_snapshot.json at {snap_json}")
    return audit_bundle, snap_json

def metric_vec(snap_json: Path) -> dict[str, float]:
    d = load_json_bom_safe(snap_json)
    m = d.get("metrics", {}) or {}
    return {
        "E": float(m.get("E", 1.0)),
        "T": float(m.get("T", 1.0)),
        "Psi": float(m.get("Psi", 1.0)),
        "Es": float(m.get("Es", 1.0)),
    }

def drift(a: dict[str, float], b: dict[str, float]) -> float:
    keys = ["E", "T", "Psi", "Es"]
    return sum(abs(a[k] - b[k]) for k in keys) / len(keys)

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--perturbations", type=int, default=3)
    args = ap.parse_args()

    outdir = Path(args.out).resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    base_smoke = outdir / "konomi_smoke_base"
    base_summary = run_smoke(base_smoke, args.quick)
    base_cov = outdir / "ucc_cov_out"
    base_bundle, base_snap = run_ucc("ucc/modules/konomi_smoke_coverage.yml", base_summary, base_cov)
    base_vec = metric_vec(base_snap)

    distances = []
    pert_results = []

    for i in range(1, max(0, args.perturbations) + 1):
        smoke_i = outdir / f"konomi_smoke_perturb_{i}"
        summary_i = run_smoke(smoke_i, args.quick)
        cov_i = outdir / f"ucc_cov_perturb_{i}"
        bundle_i, snap_i = run_ucc("ucc/modules/konomi_smoke_coverage.yml", summary_i, cov_i)
        vec_i = metric_vec(snap_i)
        d_i = drift(base_vec, vec_i)
        distances.append(d_i)
        pert_results.append({
            "i": i,
            "audit_bundle_path": str(bundle_i.relative_to(REPO)).replace("\\", "/"),
            "telemetry_snapshot_path": str(snap_i.relative_to(REPO)).replace("\\", "/"),
            "metrics": vec_i,
            "drift_from_base": d_i
        })

    deltaS = float(statistics.mean(distances)) if distances else 0.0
    lam = float(max(distances)) if distances else 0.0

    pert_path = outdir / "perturbations.json"
    pert_doc = {
        "kind": "telemetry_perturbations.v1",
        "base": {
            "audit_bundle_path": str(base_bundle.relative_to(REPO)).replace("\\", "/"),
            "telemetry_snapshot_path": str(base_snap.relative_to(REPO)).replace("\\", "/"),
            "metrics": base_vec
        },
        "perturbations": pert_results,
        "deltaS": deltaS,
        "lambda": lam
    }
    pert_path.write_text(json.dumps(pert_doc, indent=2, sort_keys=True), encoding="utf-8")

    snap = load_json_bom_safe(base_snap)
    metrics = dict(snap.get("metrics", {}) or {})
    metrics["DeltaS"] = deltaS
    metrics["Lambda"] = lam

    artifacts = [
        {"path": str(base_summary.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(base_summary)},
        {"path": str(base_bundle.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(base_bundle)},
        {"path": str(base_snap.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(base_snap)},
        {"path": str(pert_path.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(pert_path)}
    ]

    telemetry = {
        "schema_id": snap.get("schema_id", "coherencelattice.telemetry_run.v1"),
        "version": int(snap.get("version", 1)),
        "run_id": outdir.name,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "environment": {
            "python": sys.version.replace("\\n", " "),
            "platform": platform.platform(),
            "git_commit": git_commit()
        },
        "metrics": metrics,
        "flags": {
            "telemetry_ok": bool(snap.get("flags", {}).get("telemetry_ok", True)),
            "perturbations_count": len(distances),
            "deltaS_from_perturbations": deltaS,
            "lambda_from_perturbations": lam
        },
        "artifacts": artifacts,
        "ucc": {
            "audit_bundle_path": str(base_bundle.relative_to(REPO)).replace("\\", "/"),
            "audit_bundle_sha256": sha256_file(base_bundle)
        },
        "notes": f"ΔS/Λ from {len(distances)} perturbation smoke reruns."
    }

    out_json = outdir / "telemetry.json"
    out_json.write_text(json.dumps(telemetry, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[run_wrapper] wrote {out_json}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
