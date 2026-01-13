#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import shutil
import statistics
import subprocess
from pathlib import Path
from typing import Any, Dict, List

from jsonschema import Draft202012Validator

def run(cmd: List[str], cwd: Path | None = None) -> None:
    subprocess.run(cmd, cwd=str(cwd) if cwd else None, check=True)

def read_json(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def median_telemetry(run_root: Path) -> dict:
    paths = sorted(run_root.glob("run_*/telemetry.json"))
    if not paths:
        raise SystemExit(f"No telemetry.json under {run_root}")
    runs = [read_json(p) for p in paths]
    for p, r in zip(paths, runs):
        if not r.get("flags", {}).get("telemetry_ok", False):
            raise SystemExit(f"telemetry_ok false: {p}")
    keys = ["E","T","Psi","Es","DeltaS","Lambda"]
    med = {k: float(statistics.median([r["metrics"][k] for r in runs])) for k in keys}
    base = runs[0]
    base["run_id"] = run_root.name + "_median"
    base["created_at"] = "2026-01-01T00:00:00Z"
    for k,v in med.items():
        base["metrics"][k] = v
    return base

def write_json(p: Path, doc: dict) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(doc, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n")

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="out/guidance_diff", help="Output directory")
    ap.add_argument("--n", type=int, default=3, help="Replicates per side (default 3)")
    ap.add_argument("--perturbations", type=int, default=1)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--min-psi", type=float, default=0.99, help="Force proposal trigger (MVP)")
    args = ap.parse_args()

    repo = Path(".").resolve()
    out = Path(args.out).resolve()
    aroot = out / "A_unguided"
    broot = out / "B_guided"
    wtree = out / "candidate_worktree"
    branch = "guidance_candidate_worktree"

    # Clean
    if out.exists():
        shutil.rmtree(out)
    aroot.mkdir(parents=True, exist_ok=True)
    broot.mkdir(parents=True, exist_ok=True)

    py = repo / ".venv" / "Scripts" / "python.exe"
    if not py.exists():
        py = repo / ".venv" / "bin" / "python"
    if not py.exists():
        raise SystemExit("Could not find venv python in .venv")

    run_wrapper = ["tools/telemetry/run_wrapper.py"]
    reflect = ["tools/telemetry/reflect_and_propose.py"]
    validate_prop = ["tools/telemetry/validate_tuning_proposal.py"]
    apply_prop = ["tools/telemetry/apply_tuning_proposal.py"]
    build_graph = ["tools/telemetry/build_epistemic_graph.py"]
    compare = ["tools/telemetry/compare_runs.py"]

    # A runs
    for i in range(1, args.n + 1):
        run_dir = aroot / f"run_{i:02d}"
        cmd = [str(py), *run_wrapper, "--out", str(run_dir), "--perturbations", str(args.perturbations), "--emit-tel", "--emit-tel-events"]
        if args.quick: cmd.append("--quick")
        run(cmd)

    # Proposal from A last run
    prop_dir = aroot / "proposals"
    prop_dir.mkdir(parents=True, exist_ok=True)
    prop_path = aroot / "proposals" / "tuning_proposal_guidance_diff.json"
    cmd = [str(py), *reflect, "--run-dir", str(aroot / f"run_{args.n:02d}"), "--out-proposals-dir", str(prop_dir),
           "--proposal-id", "guidance_diff", "--created-at-utc", "2026-01-01T00:00:00Z", "--min-psi", str(args.min_psi)]
    out_prop = subprocess.check_output(cmd, text=True).strip()
    run([str(py), *validate_prop, out_prop])

    # Worktree + apply
    run(["git", "worktree", "prune"])
    # remove old if exists
    if wtree.exists():
        run(["git", "worktree", "remove", str(wtree), "--force"])
    # delete branch if exists (ignore failures)
    subprocess.run(["git", "branch", "-D", branch], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    run(["git", "worktree", "add", str(wtree), "-b", branch])

    # Apply proposal in worktree
    run([str(py), *apply_prop, "--proposal", out_prop, "--workdir", str(wtree), "--out-manifest", str(broot / "applied_manifest.json")])

    # B runs inside worktree (write into broot)
    for i in range(1, args.n + 1):
        run_dir = broot / f"run_{i:02d}"
        cmd = [str(py), *run_wrapper, "--out", str(run_dir), "--perturbations", str(args.perturbations), "--emit-tel", "--emit-tel-events"]
        if args.quick: cmd.append("--quick")
        run(cmd, cwd=wtree)

    # Build medians
    amed = median_telemetry(aroot)
    bmed = median_telemetry(broot)
    write_json(aroot / "telemetry_median.json", amed)
    write_json(broot / "telemetry_median.json", bmed)

    # Compare (directional)
    run([str(py), *compare, str(aroot / "telemetry_median.json"), str(broot / "telemetry_median.json"),
         "--keys", "Psi,E,T,Es,DeltaS,Lambda",
         "--nondecreasing", "Psi,E,T,Es",
         "--nonincreasing", "Lambda,DeltaS",
         "--eps", "1e-4"])

    # Build epistemic graphs for representative runs (last run)
    a_run = aroot / f"run_{args.n:02d}"
    b_run = broot / f"run_{args.n:02d}"
    run([str(py), *build_graph, "--run-dir", str(a_run), "--repo-root", str(repo)])
    run([str(py), *build_graph, "--run-dir", str(b_run), "--repo-root", str(repo)])

    # Summarize TEL step durations (optional: just count events for MVP)
    def count_jsonl(p: Path) -> int:
        if not p.exists(): return 0
        return sum(1 for line in p.read_text(encoding="utf-8").splitlines() if line.strip())

    a_tel = count_jsonl(a_run / "tel_events.jsonl")
    b_tel = count_jsonl(b_run / "tel_events.jsonl")
    a_ucc = count_jsonl(a_run / "ucc_tel_events.jsonl")
    b_ucc = count_jsonl(b_run / "ucc_tel_events.jsonl")

    report = {
        "schema": "guidance_diff_report_v1",
        "A": {"root": str(aroot).replace("\\","/"), "median": amed["metrics"], "tel_events": a_tel, "ucc_events": a_ucc},
        "B": {"root": str(broot).replace("\\","/"), "median": bmed["metrics"], "tel_events": b_tel, "ucc_events": b_ucc},
        "deltas": {k: float(bmed["metrics"][k] - amed["metrics"][k]) for k in amed["metrics"].keys()},
        "proposal": out_prop.replace("\\","/"),
        "applied_manifest": str((broot / "applied_manifest.json")).replace("\\","/"),
    }
    write_json(out / "report.json", report)

    # Cleanup worktree
    subprocess.run(["git", "worktree", "remove", str(wtree), "--force"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    subprocess.run(["git", "branch", "-D", branch], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    print(f"[guidance_diff] OK wrote {out / 'report.json'}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
