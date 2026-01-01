from __future__ import annotations

from pathlib import Path
from ucc.core import run_module

def test_nist_ai_600_1_genai_profile_pipeline_links_and_taxonomy(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    module_path = repo / "modules" / "nist_ai_600_1_genai_profile.yml"
    schema_path = repo / "schema" / "ucc_module.schema.json"
    input_path = repo / "tasks" / "nist_ai_600_1_genai_sample.json"

    outdir = tmp_path / "out"
    metrics, flags = run_module(module_path, input_path, outdir, schema_path)

    # core coverage
    assert flags["sections_complete"] is True
    assert metrics["required_count"] == 5
    assert metrics["present_count"] == 5

    # evidence links
    assert flags["evidence_links_ok"] is True
    assert metrics["evidence_link_count"] >= 1
    assert isinstance(metrics["evidence_links"], list) and len(metrics["evidence_links"]) >= 1

    # misuse taxonomy
    assert flags["misuse_taxonomy_complete"] is True
    assert metrics["misuse_coverage"] == 1.0

    # outputs
    assert (outdir / "genai_profile_checklist.md").exists()
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()
