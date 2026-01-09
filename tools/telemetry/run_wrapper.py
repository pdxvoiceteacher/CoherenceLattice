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

def git_commit() -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    except Exception:
        return "unknown"

def run(cmd: list[str], cwd: Path | None = None) -> None:
    subprocess.run(cmd, cwd=str(cwd) if cwd else None, check=True)

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True, help="Output directory for telemetry run")
    ap.add_argument("--quick", action="store_true", help="Quick mode (smoke)")
    args = ap.parse_args()

    outdir = Path(args.out).resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    # 1) Run KONOMI smoke (quick by default)
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

    # 2) Run UCC coverage against summary
    ucc_out = outdir / "ucc_cov_out"
    ucc_out.mkdir(parents=True, exist_ok=True)

    run([
        sys.executable, "-m", "ucc.cli", "run",
        "ucc/modules/konomi_smoke_coverage.yml",
        "--input", str(summary),
        "--outdir", str(ucc_out)
    ], cwd=REPO)

    audit_bundle = ucc_out / "audit_bundle.json"

    artifacts = [
        {"path": str(summary.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(summary)}
    ]
    if audit_bundle.exists():
        artifacts.append({"path": str(audit_bundle.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(audit_bundle)})

    # 3) Minimal metric placeholders (upgrade later by parsing report.json)
    metrics = {"E": 1.0, "T": 1.0, "Psi": 1.0, "DeltaS": 0.0, "Lambda": 0.0, "Es": 1.0}
    flags = {"telemetry_ok": True}

    telemetry = {
        "schema_id": "coherencelattice.telemetry_run.v1",
        "version": 1,
        "run_id": outdir.name,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "environment": {
            "python": sys.version.replace("\\n", " "),
            "platform": platform.platform(),
            "git_commit": git_commit()
        },
        "metrics": metrics,
        "flags": flags,
        "artifacts": artifacts,
        "ucc": {
            "audit_bundle_path": str(audit_bundle.relative_to(REPO)).replace("\\", "/") if audit_bundle.exists() else None,
            "audit_bundle_sha256": sha256_file(audit_bundle) if audit_bundle.exists() else None
        }
    }

    out_json = outdir / "telemetry.json"
    out_json.write_text(json.dumps(telemetry, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[run_wrapper] wrote {out_json}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
