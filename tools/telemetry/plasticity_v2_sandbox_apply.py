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
    ap.add_argument("--run-dir", required=True)
    ap.add_argument("--patch-plan-out", required=True)
    ap.add_argument("--baseline", default="tests/baselines/telemetry_smoke.baseline.json")
    ap.add_argument("--rel", type=float, default=0.02)
    ap.add_argument("--abs-floor", type=float, default=0.01)
    args = ap.parse_args()

    created_at = _now_utc_iso()
    proposal_path = Path(args.proposal)
    proposal = _load_json(proposal_path)
    pid = proposal.get("proposal_id") or "unknown"

    pp_path = Path(args.patch_plan_out)
    subprocess.run([sys.executable, "tools/telemetry/emit_patch_plan_v2.py", "--proposal", str(proposal_path), "--out", str(pp_path), "--created-at-utc", created_at], check=True)

    pp_schema = _load_json(Path("schema/plasticity_patch_plan_v2.schema.json"))
    Draft202012Validator(pp_schema).validate(_load_json(pp_path))

    # Receipt + rollback outputs
    receipt_out = Path("governance/proposals/receipts") / f"{pid}_receipt_v2_1.json"
    rollback_out = Path("governance/proposals/rollbacks") / f"{pid}_rollback_plan_v2_1.json"
    backup_dir = Path("governance/proposals/rollbacks") / pid / "backups"
    receipt_out.parent.mkdir(parents=True, exist_ok=True)
    rollback_out.parent.mkdir(parents=True, exist_ok=True)
    backup_dir.mkdir(parents=True, exist_ok=True)

    thermo_json = subprocess.check_output([
        sys.executable, "tools/telemetry/apply_patch_plan_v2.py",
        "--patch-plan", str(pp_path),
        "--repo-root", ".",
        "--receipt-out", str(receipt_out),
        "--rollback-out", str(rollback_out),
        "--backup-dir", str(backup_dir),
    ], text=True)

    thermo = json.loads(thermo_json)

    checks = {
        "pytest_ucc": _run([sys.executable, "-m", "pytest", "-q", "ucc/tests"]),
        "pytest_python": _run([sys.executable, "-m", "pytest", "-q", "python/tests"]),
        "validate_run": False,
        "compare_runs": False,
    }

    run_dir = Path(args.run_dir)
    telemetry_json = run_dir / "telemetry.json"
    if telemetry_json.exists():
        checks["validate_run"] = _run([sys.executable, "tools/telemetry/validate_run.py", str(telemetry_json), "--min-psi", "0.80", "--min-t", "0.80", "--min-es", "0.80", "--max-lambda", "0.01", "--max-deltas", "0.01"])
        baseline = Path(args.baseline)
        if baseline.exists():
            checks["compare_runs"] = _run([sys.executable, "tools/telemetry/compare_runs.py", str(baseline), str(telemetry_json), "--rel", str(args.rel), "--abs-floor", str(args.abs_floor)])
        else:
            checks["compare_runs"] = True

    reasons: List[str] = []
    if not thermo.get("allowlist_ok", False):
        reasons.append("allowlist violated")
    if not thermo.get("budget_ok", False):
        reasons.append("budget invariant violated")
    for k, ok in checks.items():
        if not ok:
            reasons.append(f"{k} failed")

    decision = "accept" if len(reasons) == 0 else "reject"
    dec = {
        "schema": "plasticity_decision_v2",
        "proposal_id": pid,
        "created_at_utc": created_at,
        "sandbox_branch": args.sandbox_branch,
        "checks": checks,
        "thermo": thermo,
        "decision": decision,
        "reasons": reasons,
        "receipt_path": str(receipt_out).replace("\\","/"),
        "rollback_plan_path": str(rollback_out).replace("\\","/"),
    }

    out_dec = Path("governance/proposals/decisions") / f"{pid}_decision_v2.json"
    _write_json(out_dec, dec)

    print(str(pp_path).replace("\\","/"))
    print(str(receipt_out).replace("\\","/"))
    print(str(rollback_out).replace("\\","/"))
    print(str(out_dec).replace("\\","/"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
