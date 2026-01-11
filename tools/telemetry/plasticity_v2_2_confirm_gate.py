from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

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
    ap.add_argument("--out-root", default="out/plasticity_v2_2")
    ap.add_argument("--baseline", default="tests/baselines/telemetry_smoke.baseline.json")
    ap.add_argument("--rel", type=float, default=0.02)
    ap.add_argument("--abs-floor", type=float, default=0.01)
    ap.add_argument("--keep-changes", action="store_true", help="Do not rollback after run B (default rolls back)")
    ap.add_argument("--created-at-utc", default="")
    args = ap.parse_args()

    created_at = args.created_at_utc.strip() or _now_utc_iso()

    proposal_path = Path(args.proposal)
    proposal = _load_json(proposal_path)
    pid = proposal.get("proposal_id") or "unknown"

    out_root = Path(args.out_root)
    run_a = out_root / "run_A"
    run_b = out_root / "run_B"
    run_a.mkdir(parents=True, exist_ok=True)
    run_b.mkdir(parents=True, exist_ok=True)

    # Emit patch plan v2 from structured recommendations
    patch_plan_path = Path("governance/proposals/queue") / f"{pid}_patch_plan_v2.json"
    subprocess.run([sys.executable, "tools/telemetry/emit_patch_plan_v2.py",
                    "--proposal", str(proposal_path),
                    "--out", str(patch_plan_path),
                    "--created-at-utc", created_at], check=True)

    pp = _load_json(patch_plan_path)
    ops = pp.get("operations") or []
    if len(ops) == 0:
        decision = {
            "schema": "plasticity_decision_v2_2",
            "proposal_id": pid,
            "created_at_utc": created_at,
            "sandbox_branch": args.sandbox_branch,
            "runs": {"run_a_dir": str(run_a).replace("\\","/"), "run_b_dir": None},
            "checks": {
                "pytest_ucc": True, "pytest_python": True,
                "validate_a": True, "validate_b": True,
                "compare_baseline_a": True, "compare_baseline_b": True,
                "compare_a_b": True
            },
            "thermo": {"allowlist_ok": True, "budget_ok": True, "notes": ["no operations"], "rollback_applied": False},
            "decision": "no_action",
            "reasons": ["patch plan contained zero operations"],
            "artifacts": {"patch_plan_path": str(patch_plan_path).replace("\\","/"), "receipt_path": None, "rollback_plan_path": None}
        }
        out_dec = Path("governance/proposals/decisions") / f"{pid}_decision_v2_2.json"
        _write_json(out_dec, decision)
        return 0

    checks = {
        "pytest_ucc": _run([sys.executable, "-m", "pytest", "-q", "ucc/tests"]),
        "pytest_python": _run([sys.executable, "-m", "pytest", "-q", "python/tests"]),
        "validate_a": False,
        "validate_b": False,
        "compare_baseline_a": False,
        "compare_baseline_b": False,
        "compare_a_b": False,
    }

    # Run A (baseline)
    ok_a = _run([sys.executable, "tools/telemetry/run_wrapper.py", "--out", str(run_a), "--quick", "--perturbations", "1", "--emit-tel", "--emit-tel-events"])
    tel_a = run_a / "telemetry.json"
    if ok_a and tel_a.exists():
        checks["validate_a"] = _run([sys.executable, "tools/telemetry/validate_run.py", str(tel_a),
                                     "--min-psi","0.80","--min-t","0.80","--min-es","0.80","--max-lambda","0.01","--max-deltas","0.01"])
        baseline = Path(args.baseline)
        checks["compare_baseline_a"] = True if not baseline.exists() else _run([sys.executable, "tools/telemetry/compare_runs.py", str(baseline), str(tel_a), "--rel", str(args.rel), "--abs-floor", str(args.abs_floor)])

    # Apply plan (receipt + rollback)
    receipt_out = Path("governance/proposals/receipts") / f"{pid}_receipt_v2_1.json"
    rollback_out = Path("governance/proposals/rollbacks") / f"{pid}_rollback_plan_v2_1.json"
    backup_dir = Path("governance/proposals/rollbacks") / pid / "backups"
    receipt_out.parent.mkdir(parents=True, exist_ok=True)
    rollback_out.parent.mkdir(parents=True, exist_ok=True)
    backup_dir.mkdir(parents=True, exist_ok=True)

    thermo_json = subprocess.check_output([
        sys.executable, "tools/telemetry/apply_patch_plan_v2.py",
        "--patch-plan", str(patch_plan_path),
        "--repo-root", ".",
        "--receipt-out", str(receipt_out),
        "--rollback-out", str(rollback_out),
        "--backup-dir", str(backup_dir),
    ], text=True)
    thermo = json.loads(thermo_json)

    # Run B (after apply)
    ok_b = _run([sys.executable, "tools/telemetry/run_wrapper.py", "--out", str(run_b), "--quick", "--perturbations", "1", "--emit-tel", "--emit-tel-events"])
    tel_b = run_b / "telemetry.json"
    if ok_b and tel_b.exists():
        checks["validate_b"] = _run([sys.executable, "tools/telemetry/validate_run.py", str(tel_b),
                                     "--min-psi","0.80","--min-t","0.80","--min-es","0.80","--max-lambda","0.01","--max-deltas","0.01"])
        baseline = Path(args.baseline)
        checks["compare_baseline_b"] = True if not baseline.exists() else _run([sys.executable, "tools/telemetry/compare_runs.py", str(baseline), str(tel_b), "--rel", str(args.rel), "--abs-floor", str(args.abs_floor)])
        # Compare A vs B
        if tel_a.exists():
            checks["compare_a_b"] = _run([sys.executable, "tools/telemetry/compare_runs.py", str(tel_a), str(tel_b), "--rel", str(args.rel), "--abs-floor", str(args.abs_floor)])

    # Auto-rollback by default (keeps working tree clean)
    rollback_applied = False
    if (not args.keep_changes) and rollback_out.exists():
        rbr = subprocess.run([sys.executable, "tools/telemetry/apply_rollback_plan_v2_1.py", "--rollback-plan", str(rollback_out), "--repo-root", ".", "--apply"], text=True)
        rollback_applied = (rbr.returncode == 0)

    thermo_block = {
        "allowlist_ok": bool(thermo.get("allowlist_ok", False)),
        "budget_ok": bool(thermo.get("budget_ok", False)),
        "notes": list(thermo.get("notes", [])),
        "rollback_applied": bool(rollback_applied),
    }

    reasons: List[str] = []
    if not thermo_block["allowlist_ok"]:
        reasons.append("allowlist violated")
    if not thermo_block["budget_ok"]:
        reasons.append("budget invariant violated")
    for k, ok in checks.items():
        if not ok:
            reasons.append(f"{k} failed")

    decision_str = "accept" if len(reasons) == 0 else "reject"

    decision = {
        "schema": "plasticity_decision_v2_2",
        "proposal_id": pid,
        "created_at_utc": created_at,
        "sandbox_branch": args.sandbox_branch,
        "runs": {"run_a_dir": str(run_a).replace("\\","/"), "run_b_dir": str(run_b).replace("\\","/")},
        "checks": checks,
        "thermo": thermo_block,
        "decision": decision_str,
        "reasons": reasons,
        "artifacts": {
            "patch_plan_path": str(patch_plan_path).replace("\\","/"),
            "receipt_path": str(receipt_out).replace("\\","/") if receipt_out.exists() else None,
            "rollback_plan_path": str(rollback_out).replace("\\","/") if rollback_out.exists() else None
        }
    }

    # Validate decision schema
    schema = _load_json(Path("schema/plasticity_decision_v2_2.schema.json"))
    Draft202012Validator(schema).validate(decision)

    out_dec = Path("governance/proposals/decisions") / f"{pid}_decision_v2_2.json"
    _write_json(out_dec, decision)

    print(str(out_dec).replace("\\","/"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
