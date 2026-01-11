import json
import subprocess
import sys
from pathlib import Path

def test_apply_patch_plan_v2_emits_receipt_and_rollback(tmp_path: Path):
    # Create a fake repo root with allowlisted config file
    repo = tmp_path / "repo"
    (repo / "config" / "plasticity").mkdir(parents=True)
    cfg = repo / "config" / "plasticity" / "tuning.json"
    cfg.write_text(json.dumps({"min_psi_threshold": 0.90, "max_proposals_per_run": 1, "max_sandbox_attempts": 1}, indent=2, sort_keys=True) + "\n",
                   encoding="utf-8", newline="\n")

    plan = {
        "schema": "plasticity_patch_plan_v2",
        "proposal_id": "pid",
        "created_at_utc": "2026-01-01T00:00:00Z",
        "guardrails": {
            "allow_prefixes": ["config/plasticity/","governance/","schema/"],
            "deny_prefixes": [".github/","tools/","ucc/","python/","config/"],
            "budget_keys": ["perturb","retry","timeout","concurrency","parallel","workers","matrix","interval","freq","schedule","max_","attempt","budget"]
        },
        "operations": [
            {"op":"json_set","path":"config/plasticity/tuning.json","json_path":"min_psi_threshold","value":0.89,"note":"test"}
        ]
    }
    plan_path = tmp_path / "plan.json"
    plan_path.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")

    receipt = tmp_path / "receipt.json"
    rollback = tmp_path / "rollback.json"

    # Run the tool from repo root, but target repo is tmp_path/repo
    subprocess.run([
        sys.executable, "tools/telemetry/apply_patch_plan_v2.py",
        "--patch-plan", str(plan_path),
        "--repo-root", str(repo),
        "--receipt-out", str(receipt),
        "--rollback-out", str(rollback)
    ], check=True, cwd=Path.cwd())

    assert receipt.exists()
    assert rollback.exists()

    r = json.loads(receipt.read_text(encoding="utf-8"))
    assert r["schema"] == "plasticity_receipt_v2_1"
    assert r["thermo"]["allowlist_ok"] is True
    assert r["thermo"]["budget_ok"] is True
    assert len(r["file_changes"]) == 1
    assert r["file_changes"][0]["before_hash"] != r["file_changes"][0]["after_hash"]

    rb = json.loads(rollback.read_text(encoding="utf-8"))
    assert rb["schema"] == "plasticity_rollback_plan_v2_1"
    assert len(rb["operations"]) == 1
    op = rb["operations"][0]
    assert op["op"] == "json_set"
    assert op["path"] == "config/plasticity/tuning.json"
    assert op["json_path"] == "min_psi_threshold"
    assert op["value"] == 0.90
