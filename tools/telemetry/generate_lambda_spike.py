#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
from datetime import datetime, timezone
from pathlib import Path
import sys


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def git_commit(repo: Path) -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=str(repo), stderr=subprocess.DEVNULL).decode().strip()
    except Exception:
        return "0000000"


def write_telemetry(run_dir: Path, artifact_path: Path, lambda_value: float, repo_root: Path) -> None:
    metrics = {
        "E": 0.62,
        "T": 0.71,
        "Es": 0.84,
    }
    metrics["Psi"] = round(metrics["E"] * metrics["T"], 6)
    metrics["DeltaS"] = 0.08
    metrics["Lambda"] = float(lambda_value)

    env = {
        "python": sys.version.replace("\n", " "),
        "platform": platform.platform(),
        "git_commit": git_commit(repo_root),
    }

    artifacts = [{
        "path": str(artifact_path).replace("\\", "/"),
        "sha256": sha256_file(artifact_path),
    }]

    telemetry = {
        "schema_id": "coherencelattice.telemetry_run.v1",
        "version": 1,
        "run_id": run_dir.name,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "environment": env,
        "metrics": metrics,
        "flags": {
            "telemetry_ok": True,
            "lambda_from_perturbations": metrics["Lambda"],
        },
        "artifacts": artifacts,
        "notes": "Synthetic Lambda spike run for experiment 2A.",
    }

    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "telemetry.json").write_text(json.dumps(telemetry, indent=2) + "\n", encoding="utf-8")

    meta = {
        "lambda": float(lambda_value),
        "lambda_warn": 0.80,
        "lambda_gate": "review" if float(lambda_value) >= 0.80 else "proceed",
    }
    evt = {"seq": 1, "kind": "ucc_lambda_metrics", "data": {"metrics": metrics, "meta": meta}}
    (run_dir / "ucc_tel_events.jsonl").write_text(json.dumps(evt, ensure_ascii=False) + "\n", encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--submission-dir", default="examples/submission_lambda_spike")
    ap.add_argument("--lambda-guided", type=float, default=0.85)
    ap.add_argument("--lambda-unguided", type=float, default=0.20)
    args = ap.parse_args()

    subdir = Path(args.submission_dir).resolve()
    artifacts_dir = subdir / "artifacts"
    drift_path = artifacts_dir / "drift_series.json"
    if not drift_path.exists():
        raise SystemExit(f"Missing artifact: {drift_path}")

    guided_run = subdir / "runs" / "guided"
    unguided_run = subdir / "runs" / "unguided"

    repo_root = Path(__file__).resolve().parents[2]

    write_telemetry(unguided_run, drift_path, args.lambda_unguided, repo_root)
    write_telemetry(guided_run, drift_path, args.lambda_guided, repo_root)

    print(f"[lambda_spike] wrote {unguided_run / 'telemetry.json'}")
    print(f"[lambda_spike] wrote {guided_run / 'telemetry.json'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
