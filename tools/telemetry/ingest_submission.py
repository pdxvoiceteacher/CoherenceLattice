#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict, List

from jsonschema import Draft202012Validator


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def run_py(py: Path, args: List[str], cwd: Path) -> None:
    import subprocess
    subprocess.run([str(py), *args], cwd=str(cwd), check=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--submission-dir", required=True, help="Folder containing submission.json")
    ap.add_argument("--repo-root", default=".", help="Repo root for running tools and schema paths")
    ap.add_argument("--out", default="", help="Output path (default: <submission-dir>/ingest_report.json)")
    args = ap.parse_args()

    repo = Path(args.repo_root).resolve()
    subdir = Path(args.submission_dir).resolve()
    sub_json = subdir / "submission.json"
    if not sub_json.exists():
        raise SystemExit(f"[ingest_submission] FAIL missing {sub_json}")

    py = repo / ".venv" / "Scripts" / "python.exe"
    if not py.exists():
        py = repo / ".venv" / "bin" / "python"
    if not py.exists():
        raise SystemExit("[ingest_submission] FAIL cannot find .venv python")

    sub_schema = load_json(repo / "schema" / "submission.schema.json")
    doc = load_json(sub_json)
    Draft202012Validator(sub_schema).validate(doc)

    runs = doc["runs"]
    results: List[Dict[str, Any]] = []

    for label, spec in runs.items():
        run_path = (subdir / spec["path"]).resolve()
        tele = run_path / "telemetry.json"
        if not tele.exists():
            results.append({"label": label, "path": str(run_path), "status": "fail", "error": "missing telemetry.json"})
            continue

        try:
            run_py(py, ["tools/telemetry/verify_artifacts.py", str(tele), "--repo-root", str(repo)], cwd=repo)
            run_py(py, ["tools/telemetry/validate_claims.py", str(tele), "--repo-root", str(repo)], cwd=repo)

            tel_events = run_path / "tel_events.jsonl"
            if tel_events.exists():
                run_py(py, ["tools/telemetry/validate_jsonl.py", str(tel_events), "--require-keys", "event,name,ts,run_id"], cwd=repo)
            
            ucc_events = run_path / "ucc_tel_events.jsonl"
            if not ucc_events.exists():
                ucc_events.write_text("", encoding="utf-8", newline="\n")

            ucc_events = run_path / "ucc_tel_events.jsonl"
            if ucc_events.exists():
                run_py(py, ["tools/telemetry/validate_jsonl.py", str(ucc_events)], cwd=repo)
                
            run_py(py, ["tools/telemetry/build_epistemic_graph.py", "--run-dir", str(run_path), "--repo-root", str(repo)], cwd=repo)
            sophia_args = [
                "tools/telemetry/sophia_audit.py",
                "--run-dir",
                str(run_path),
                "--repo-root",
                str(repo),
            ]
            if spec.get("audit_sophia"):
                sophia_args.append("--audit-sophia")
            run_py(py, sophia_args, cwd=repo)

            results.append({"label": label, "path": str(run_path), "status": "ok"})
        except Exception as e:
            results.append({"label": label, "path": str(run_path), "status": "fail", "error": repr(e)})

        # Generate a submission receipt (canonical manifest SHA256) for reviewer trust
    try:
        run_py(py, ["tools/telemetry/make_submission_receipt.py", "--submission-dir", str(subdir)], cwd=repo)
    except Exception as e:
        # Receipt generation should not hide failures; record it in results instead
        results.append({"label": "_receipt", "path": str(subdir), "status": "fail", "error": "receipt_generation_failed: " + repr(e)})

    # Generate submission receipt (canonical manifest SHA256)
    try:
        run_py(py, ["tools/telemetry/make_submission_receipt.py", "--submission-dir", str(subdir)], cwd=repo)
    except Exception as e:
        results.append({
            "label": "_receipt",
            "path": str(subdir),
            "status": "fail",
            "error": "receipt_generation_failed: " + repr(e),
        })

    report = {
        "schema": "ingest_report_v1",
        "submission": str(sub_json).replace("\\\\", "/"),
        "title": doc.get("title"),
        "results": results,
    }

    outp = Path(args.out) if args.out else (subdir / "ingest_report.json")
    outp.write_text(
        json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )

    print(f"[ingest_submission] OK wrote {outp}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
