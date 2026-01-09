#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, platform, subprocess, sys
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

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True, help="Output directory for telemetry run")
    ap.add_argument("--quick", action="store_true", help="Quick mode (smoke)")
    args = ap.parse_args()

    outdir = Path(args.out).resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    # 1) Run KONOMI smoke
    smoke_out = outdir / "konomi_smoke_out"
    smoke_out.mkdir(parents=True, exist_ok=True)

    run([
        sys.executable,
        "python/experiments/konomi_smoke/run_smoke.py",
        "--quick" if args.quick else "--full",
        "--outdir",
        str(smoke_out)
    ], cwd=REPO)

    summary = smoke_out / "konomi_smoke_summary.json"
    if not summary.exists():
        raise SystemExit(f"Missing expected smoke summary: {summary}")

    # 2) Run coverage module (produces audit_bundle.json)
    cov_out = outdir / "ucc_cov_out"
    cov_out.mkdir(parents=True, exist_ok=True)

    run([
        sys.executable, "-m", "ucc.cli", "run",
        "ucc/modules/konomi_smoke_coverage.yml",
        "--input", str(summary),
        "--outdir", str(cov_out)
    ], cwd=REPO)

    audit_bundle = cov_out / "audit_bundle.json"
    if not audit_bundle.exists():
        raise SystemExit(f"Missing expected UCC audit_bundle.json: {audit_bundle}")

    # 3) Canonical telemetry snapshot module (input = audit_bundle.json)
    snap_out = outdir / "telemetry_snapshot_out"
    snap_out.mkdir(parents=True, exist_ok=True)

    run([
        sys.executable, "-m", "ucc.cli", "run",
        "ucc/modules/telemetry_snapshot_v1.yml",
        "--input", str(audit_bundle),
        "--outdir", str(snap_out)
    ], cwd=REPO)

    snap_json = snap_out / "telemetry_snapshot.json"
    if not snap_json.exists():
        raise SystemExit(f"Missing expected telemetry_snapshot.json: {snap_json}")

    snap = load_json_bom_safe(snap_json)

    # 4) Build final telemetry.json (canonical metrics + full artifact hashing)
    artifacts = [
        {"path": str(summary.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(summary)},
        {"path": str(audit_bundle.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(audit_bundle)},
        {"path": str(snap_json.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(snap_json)}
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
        "metrics": snap.get("metrics", {"E":1.0,"T":1.0,"Psi":1.0,"DeltaS":0.0,"Lambda":0.0,"Es":1.0}),
        "flags": snap.get("flags", {"telemetry_ok": True}),
        "artifacts": artifacts,
        "ucc": {
            "audit_bundle_path": str(audit_bundle.relative_to(REPO)).replace("\\", "/"),
            "audit_bundle_sha256": sha256_file(audit_bundle)
        },
        "notes": "telemetry.json uses canonical metrics from telemetry_snapshot_v1"
    }

    out_json = outdir / "telemetry.json"
    out_json.write_text(json.dumps(telemetry, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[run_wrapper] wrote {out_json}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
