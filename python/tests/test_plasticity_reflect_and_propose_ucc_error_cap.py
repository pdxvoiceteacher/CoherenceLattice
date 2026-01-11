import json
import subprocess
import sys
from pathlib import Path

def test_cap_max_proposals_on_ucc_error_even_if_psi_ok(tmp_path: Path):
    run_dir = tmp_path / "run"
    run_dir.mkdir()

    # Psi is fine
    telemetry = {
        "coherence_metrics": {"Psi": 0.99, "E": 0.95, "T": 1.0, "Es": 1.0, "DeltaS": 0.0, "Lambda": 0.0},
        "tel_summary": {"schema":"tel_summary_v1","tel_schema":"tel_graph_v1","graph_id":"x","fingerprint_sha256":"abc",
                        "nodes_total": 10, "edges_total": 9, "nodes_by_band":{"STM":1,"MTM":2,"LTM":7},"edges_by_kind":{}}
    }
    (run_dir / "telemetry.json").write_text(json.dumps(telemetry, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    (run_dir / "tel_events.jsonl").write_text('{"seq":1,"kind":"tel","data":{}}\n', encoding="utf-8", newline="\n")

    # UCC error present
    (run_dir / "ucc_tel_events.jsonl").write_text('{"seq":1,"kind":"ucc_step_error","data":{"error":"x"}}\n', encoding="utf-8", newline="\n")

    tuning = tmp_path / "tuning.json"
    tuning.write_text(json.dumps({"min_psi_threshold": 0.90, "max_proposals_per_run": 3, "max_sandbox_attempts": 1}, indent=2, sort_keys=True) + "\n",
                      encoding="utf-8", newline="\n")

    out_props = tmp_path / "props"
    out_props.mkdir()

    cmd = [
        sys.executable,
        "tools/telemetry/reflect_and_propose.py",
        "--run-dir", str(run_dir),
        "--out-proposals-dir", str(out_props),
        "--force-proposal",
        "--proposal-id", "test",
        "--created-at-utc", "2026-01-01T00:00:00Z",
        "--min-psi", "0.90",
        "--tuning-config", str(tuning),
        "--tune-step", "0.01",
    ]
    r = subprocess.run(cmd, check=True, capture_output=True, text=True)
    out_path = Path(r.stdout.strip())
    doc = json.loads(out_path.read_text(encoding="utf-8"))
    recs = doc.get("recommendations", [])
    actions = [rr.get("action_v2") for rr in recs if isinstance(rr, dict) and isinstance(rr.get("action_v2"), dict)]
    assert any(a.get("json_path") == "max_proposals_per_run" and a.get("value") == 1 for a in actions)
