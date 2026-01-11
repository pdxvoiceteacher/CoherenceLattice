from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

from jsonschema import Draft202012Validator


def _now_utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _run(cmd: List[str]) -> bool:
    r = subprocess.run(cmd, text=True)
    return r.returncode == 0


def _load_json(p: Path) -> Dict[str, Any]:
    return json.loads(p.read_text(encoding="utf-8"))


def _write_json(p: Path, obj: Any) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--proposal", required=True)
    ap.add_argument("--sandbox-branch", required=True)
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--baseline", default="tests/baselines/telemetry_smoke.baseline.json")
    ap.add_argument("--rel", type=float, default=0.02)
    ap.add_argument("--abs-floor", type=float, default=0.01)
    ap.add_argument("--min-psi", type=float, default=0.80)
    ap.add_argument("--min-t", type=float, default=0.80)
    ap.add_argument("--min-es", type=float, default=0.80)
    ap.add_argument("--max-lambda", type=float, default=0.01)
    ap.add_argument("--max-deltas", type=float, default=0.01)
    args = ap.parse_args()

    proposal_path = Path(args.proposal)
    proposal = _load_json(proposal_path)
    pid = proposal.get("proposal_id") or "unknown"

    created_at = _now_utc_iso()

    # v1: create a patch plan artifact (no code edits yet; operations can be extended later)
    plan = {
        "schema": "plasticity_patch_plan_v1",
        "proposal_id": pid,
        "created_at_utc": created_at,
        "operations": [
            {
                "op": "noop",
                "path": "",
                "content": None,
                "pattern": None,
                "replacement": None,
                "json_path": None,
                "value": None
            }
        ],
        "notes": {
            "intent": "v1 sandbox apply plan (no auto-modifications yet). Extend operations to apply real tuning changes.",
            "proposal_source": str(proposal_path).replace("\\", "/")
        }
    }

    # Write patch plan into governance queue so it can be versioned
    patch_plan_path = Path("governance/proposals/queue") / f"{pid}_patch_plan.json"
    _write_json(patch_plan_path, plan)

    # Validate patch plan schema
    plan_schema = _load_json(Path("schema/plasticity_patch_plan.schema.json"))
    Draft202012Validator(plan_schema).validate(plan)

    # Run checks in this sandbox branch working tree
    checks = {
        "pytest_ucc": _run([sys.executable, "-m", "pytest", "-q", "ucc/tests"]),
        "pytest_python": _run([sys.executable, "-m", "pytest", "-q", "python/tests"]),
        "validate_run": False,
        "compare_runs": False,
    }

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    # Telemetry smoke
    ok_smoke = _run([
        sys.executable,
        "tools/telemetry/run_wrapper.py",
        "--out", str(out_dir),
        "--quick",
        "--perturbations", "1",
        "--emit-tel",
        "--emit-tel-events",
    ])

    telemetry_json = out_dir / "telemetry.json"
    if ok_smoke and telemetry_json.exists():
        checks["validate_run"] = _run([
            sys.executable,
            "tools/telemetry/validate_run.py",
            str(telemetry_json),
            "--min-psi", str(args.min_psi),
            "--min-t", str(args.min_t),
            "--min-es", str(args.min_es),
            "--max-lambda", str(args.max_lambda),
            "--max-deltas", str(args.max_deltas),
        ])

        baseline = Path(args.baseline)
        if baseline.exists():
            checks["compare_runs"] = _run([
                sys.executable,
                "tools/telemetry/compare_runs.py",
                str(baseline),
                str(telemetry_json),
                "--rel", str(args.rel),
                "--abs-floor", str(args.abs_floor),
            ])
        else:
            checks["compare_runs"] = True  # no baseline available => do not block

    reasons: List[str] = []
    if not checks["pytest_ucc"]:
        reasons.append("ucc tests failed")
    if not checks["pytest_python"]:
        reasons.append("python tests failed")
    if not checks["validate_run"]:
        reasons.append("validate_run failed")
    if not checks["compare_runs"]:
        reasons.append("compare_runs failed")

    if len(reasons) == 0:
        decision = "accept"
    else:
        decision = "reject"

    dec = {
        "schema": "plasticity_decision_v1",
        "proposal_id": pid,
        "created_at_utc": created_at,
        "sandbox_branch": args.sandbox_branch,
        "checks": checks,
        "decision": decision,
        "reasons": reasons,
    }

    decision_path = Path("governance/proposals/decisions") / f"{pid}_decision.json"
    _write_json(decision_path, dec)

    dec_schema = _load_json(Path("schema/plasticity_decision.schema.json"))
    Draft202012Validator(dec_schema).validate(dec)

    print(str(patch_plan_path).replace("\\","/"))
    print(str(decision_path).replace("\\","/"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
