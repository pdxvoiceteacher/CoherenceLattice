from __future__ import annotations

from pathlib import Path
from ucc.core import run_module


def test_konomi_api_audit_summary_coverage(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    module_path = repo / "modules" / "konomi_api_audit_summary_coverage.yml"
    schema_path = repo / "schema" / "ucc_module.schema.json"
    input_path = repo / "tasks" / "konomi_api_audit_summary_sample.json"

    outdir = tmp_path / "out"
    metrics, flags = run_module(module_path, input_path, outdir, schema_path)

    assert flags["sections_complete"] is True
    assert (outdir / "api_audit_summary_checklist.md").exists()
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()
