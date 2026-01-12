import json
import subprocess
import sys
from pathlib import Path

def test_tel_nodes_high_caps_proposals(tmp_path: Path):
    run_dir = tmp_path / "run"
    run_dir.mkdir()

    telemetry = {
        "coherence_metrics": {"Psi": 0.99},
        "tel_summary": {"schema":"tel_summary_v1","tel_schema":"tel_graph_v1","graph_id":"x","fingerprint_sha256":"abc",
                        "nodes_total": 999, "edges_total": 10, "nodes_by_band":{"STM":1,"MTM":2,"LTM":7},"edges_by_kind":{}}
    }
    (run_dir / "telemetry.json").write_text(json.dumps(telemetry, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    (run_dir / "tel_events.jsonl").write_text('{"seq":1,"kind":"tel","data":{}}\n', encoding="utf-8", newline="\n")
    (run_dir / "ucc_tel_events.jsonl").write_text('', encoding="utf-8", newline="\n")

    tuning = tmp_path / "tuning.json"
    tuning.write_text(json.dumps({"max_proposals_per_run": 3, "max_sandbox_attempts": 2, "max_tel_nodes": 100}, indent=2, sort_keys=True) + "\n",
                      encoding="utf-8", newline="\n")

    out_props = tmp_path / "props"
    out_props.mkdir()

    r = subprocess.run([
        sys.executable, "tools/telemetry/reflect_and_propose.py",
        "--run-dir", str(run_dir),
        "--out-proposals-dir", str(out_props),
        "--force-proposal",
        "--proposal-id", "test",
        "--created-at-utc", "2026-01-01T00:00:00Z",
        "--tuning-config", str(tuning),
    ], check=True, capture_output=True, text=True)

    doc = json.loads(Path(r.stdout.strip()).read_text(encoding="utf-8"))
    actions = [rr.get("action_v2") for rr in doc.get("recommendations", []) if isinstance(rr, dict) and isinstance(rr.get("action_v2"), dict)]
    assert any(a.get("json_path") == "max_proposals_per_run" and a.get("value") == 1 for a in actions)
    assert any(a.get("json_path") == "max_sandbox_attempts" and a.get("value") == 1 for a in actions)

def test_ucc_events_high_caps_sandbox(tmp_path: Path):
    run_dir = tmp_path / "run"
    run_dir.mkdir()

    telemetry = {
        "coherence_metrics": {"Psi": 0.99},
        "tel_summary": {"schema":"tel_summary_v1","tel_schema":"tel_graph_v1","graph_id":"x","fingerprint_sha256":"abc",
                        "nodes_total": 10, "edges_total": 10, "nodes_by_band":{"STM":1,"MTM":2,"LTM":7},"edges_by_kind":{}}
    }
    (run_dir / "telemetry.json").write_text(json.dumps(telemetry, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    (run_dir / "tel_events.jsonl").write_text('', encoding="utf-8", newline="\n")

    # 11 events, threshold 10
    lines = "\n".join(['{"seq":%d,"kind":"ucc_step_end","data":{}}' % i for i in range(1, 12)]) + "\n"
    (run_dir / "ucc_tel_events.jsonl").write_text(lines, encoding="utf-8", newline="\n")

    tuning = tmp_path / "tuning.json"
    tuning.write_text(json.dumps({"max_proposals_per_run": 1, "max_sandbox_attempts": 2, "max_ucc_events_total": 10}, indent=2, sort_keys=True) + "\n",
                      encoding="utf-8", newline="\n")

    out_props = tmp_path / "props"
    out_props.mkdir()

    r = subprocess.run([
        sys.executable, "tools/telemetry/reflect_and_propose.py",
        "--run-dir", str(run_dir),
        "--out-proposals-dir", str(out_props),
        "--force-proposal",
        "--proposal-id", "test2",
        "--created-at-utc", "2026-01-01T00:00:00Z",
        "--tuning-config", str(tuning),
    ], check=True, capture_output=True, text=True)

    doc = json.loads(Path(r.stdout.strip()).read_text(encoding="utf-8"))
    actions = [rr.get("action_v2") for rr in doc.get("recommendations", []) if isinstance(rr, dict) and isinstance(rr.get("action_v2"), dict)]
    assert any(a.get("json_path") == "max_sandbox_attempts" and a.get("value") == 1 for a in actions)
