from __future__ import annotations
from pathlib import Path
import subprocess
import sys

REPO = Path(__file__).resolve().parents[1]

def run(cmd: list[str]) -> str:
    p = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True)
    if p.returncode != 0:
        raise AssertionError(f"Command failed:\n{cmd}\nSTDOUT:\n{p.stdout}\nSTDERR:\n{p.stderr}")
    return p.stdout + p.stderr

def test_lambda_deltaS_guided_not_worse_than_unguided() -> None:
    py = sys.executable

    # Ensure ingest has been run in CI elsewhere; if not, we can run it here.
    sub = REPO / "examples" / "submission_demo"
    ung = sub / "runs" / "unguided" / "telemetry.json"
    gui = sub / "runs" / "guided" / "telemetry.json"

    assert ung.exists(), f"Missing {ung}"
    assert gui.exists(), f"Missing {gui}"

    out = run([py, "tools/telemetry/analyze_lambda_deltaS.py", str(ung), str(gui)])
    assert "OK" in out
