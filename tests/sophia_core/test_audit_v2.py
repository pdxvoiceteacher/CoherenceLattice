import json
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[2]
SOPHIA_SRC = REPO_ROOT / "sophia-core" / "src"
if str(SOPHIA_SRC) not in sys.path:
    sys.path.insert(0, str(SOPHIA_SRC))

from sophia_core.audit import run_audit_v2


@pytest.fixture()
def telemetry_base():
    return {
        "run_id": "run-1",
        "metrics": {"Psi": 0.8, "E": 0.7, "T": 0.85, "DeltaS": 0.05, "Lambda": 0.1},
        "claims": [
            {
                "id": "c1",
                "type": "descriptive",
                "statement": "System X is stable.",
                "confidence": 0.6,
                "evidence": ["runs/demo/artifact.txt"],
            },
            {
                "id": "c2",
                "type": "descriptive",
                "statement": "System X is not stable.",
                "confidence": 0.6,
            },
        ],
    }


@pytest.fixture()
def graph_base():
    return {"nodes": []}


def test_audit_history_regression(tmp_path, telemetry_base, graph_base):
    history_path = tmp_path / "history_summary.json"

    report_1 = run_audit_v2(
        telemetry_base,
        graph_base,
        repo_root=REPO_ROOT,
        history_path=history_path,
    )
    assert report_1.trend_summary["history_count"] == 0

    telemetry_2 = json.loads(json.dumps(telemetry_base))
    telemetry_2["run_id"] = "run-2"
    telemetry_2["metrics"]["Psi"] = 0.7
    telemetry_2["metrics"]["Lambda"] = 0.25

    report_2 = run_audit_v2(
        telemetry_2,
        graph_base,
        repo_root=REPO_ROOT,
        history_path=history_path,
    )
    assert report_2.trend_summary["history_count"] == 1
    assert any(f.type == "coherence_regression" for f in report_2.findings)


def test_audit_contradictions(telemetry_base, graph_base, tmp_path):
    report = run_audit_v2(
        telemetry_base,
        graph_base,
        repo_root=REPO_ROOT,
        history_path=tmp_path / "history_summary.json",
    )
    assert report.contradictions
    assert any(f.type == "contradiction" for f in report.findings)


def test_repair_suggestions_for_missing_evidence(tmp_path):
    telemetry = {
        "run_id": "run-3",
        "metrics": {"Psi": 0.8},
        "claims": [
            {
                "id": "c3",
                "type": "descriptive",
                "statement": "Artifact A supports the claim.",
                "confidence": 0.5,
                "evidence": ["runs/demo/missing.txt"],
            }
        ],
    }
    graph = {"nodes": []}

    report = run_audit_v2(
        telemetry,
        graph,
        repo_root=REPO_ROOT,
        history_path=tmp_path / "history_summary.json",
    )
    assert report.repair_suggestions
    assert report.repair_suggestions[0].id == "suggestion_evidence_registry"
