import json
import subprocess
import sys
from pathlib import Path

def test_apply_rollback_plan_restores_json(tmp_path: Path):
    repo = tmp_path / "repo"
    (repo / "config" / "plasticity").mkdir(parents=True)
    cfg = repo / "config" / "plasticity" / "tuning.json"
    cfg.write_text(json.dumps({"min_psi_threshold": 0.89}, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")

    rb = {
        "schema": "plasticity_rollback_plan_v2_1",
        "proposal_id": "pid",
        "created_at_utc": "2026-01-01T00:00:00Z",
        "patch_plan_path": "x",
        "operations": [
            {"op":"json_set","path":"config/plasticity/tuning.json","json_path":"min_psi_threshold","value":0.90,"backup_path":None,"note":"rb"}
        ]
    }
    rb_path = tmp_path / "rb.json"
    rb_path.write_text(json.dumps(rb, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")

    subprocess.run([sys.executable, "tools/telemetry/apply_rollback_plan_v2_1.py", "--rollback-plan", str(rb_path), "--repo-root", str(repo), "--apply"], check=True)

    doc = json.loads(cfg.read_text(encoding="utf-8"))
    assert doc["min_psi_threshold"] == 0.90
