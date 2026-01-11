import json
import subprocess
import sys
from pathlib import Path

def test_reflect_and_propose_emits_schema_valid_proposal(tmp_path: Path):
    run_dir = tmp_path / "run"
    run_dir.mkdir()

    # minimal telemetry.json
    telemetry = {
        "coherence_metrics": {"Psi": 0.85, "E": 0.95, "T": 1.0, "Es": 1.0, "DeltaS": 0.0, "Lambda": 0.0},
        "tel_summary": {"nodes_total": 10, "edges_total": 9, "schema": "tel_summary_v1", "tel_schema": "tel_graph_v1", "graph_id": "x", "fingerprint_sha256": "abc", "nodes_by_band": {"STM": 1, "MTM": 2, "LTM": 7}, "edges_by_kind": {}}
    }
    (run_dir / "telemetry.json").write_text(json.dumps(telemetry, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")

    # event logs
    (run_dir / "tel_events.jsonl").write_text('{"seq":1,"kind":"tel","data":{}}\n', encoding="utf-8", newline="\n")
    (run_dir / "ucc_tel_events.jsonl").write_text('{"seq":1,"kind":"ucc_step_error","data":{"error":"x"}}\n', encoding="utf-8", newline="\n")

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
    ]
    r = subprocess.run(cmd, check=True, capture_output=True, text=True)
    out_path = Path(r.stdout.strip())
    assert out_path.exists()

    # validate schema
    subprocess.run([sys.executable, "tools/telemetry/validate_tuning_proposal.py", str(out_path)], check=True)
