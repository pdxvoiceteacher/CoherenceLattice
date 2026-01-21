import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
SOPHIA_SRC = REPO_ROOT / "sophia-core" / "src"
if str(SOPHIA_SRC) not in sys.path:
    sys.path.insert(0, str(SOPHIA_SRC))

from sophia_core.audit import run_audit_v3


@pytest.fixture()
def graph_base():
    return {"nodes": []}


def test_v3_trajectory_and_ethics(tmp_path, graph_base):
    telemetry = {
        "run_id": "run-trajectory",
        "metrics": {"Psi": 0.55, "E": 0.4, "T": 0.5, "DeltaS": 0.2, "Lambda": 0.7},
        "claims": [],
    }
    report = run_audit_v3(
        telemetry,
        graph_base,
        repo_root=REPO_ROOT,
        history_path=tmp_path / "history.json",
        kernel_path=tmp_path / "kernel.json",
        calibrate_trajectories=True,
        ethics_check=True,
        memory_aware=False,
    )
    assert report.trajectory_phase in ("warning", "critical")
    assert report.ethical_symmetry is not None
    assert any(f.type in ("coherence_drift", "ethical_symmetry_violation") for f in report.findings)


def test_v3_memory_drift(tmp_path, graph_base):
    telemetry = {
        "run_id": "run-memory",
        "metrics": {"Psi": 0.9, "E": 0.8, "T": 0.9, "DeltaS": 0.1, "Lambda": 0.1},
        "claims": [],
    }
    kernel_path = tmp_path / "kernel.json"
    run_audit_v3(
        telemetry,
        graph_base,
        repo_root=REPO_ROOT,
        history_path=tmp_path / "history.json",
        kernel_path=kernel_path,
        memory_aware=True,
    )

    telemetry_shift = {
        "run_id": "run-memory-2",
        "metrics": {"Psi": 0.2, "E": 0.3, "T": 0.4, "DeltaS": 0.1, "Lambda": 0.9},
        "claims": [],
    }
    report = run_audit_v3(
        telemetry_shift,
        graph_base,
        repo_root=REPO_ROOT,
        history_path=tmp_path / "history.json",
        kernel_path=kernel_path,
        memory_aware=True,
    )
    assert report.memory_drift_flag
    assert any(f.type == "memory_deviation" for f in report.findings)
