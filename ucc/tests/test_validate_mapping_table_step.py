from __future__ import annotations

from pathlib import Path
from ucc.core import run_module

def test_validate_mapping_table_step(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"
    module_path = repo / "modules" / "mapping_table_validate.yml"
    input_path = repo / "authorities" / "mappings" / "ci_validate_mapping_sample.csv"

    outdir = tmp_path / "mapping_out"
    metrics, flags = run_module(module_path, input_path, outdir, schema)

    assert flags.get("mapping_table_ok") is True
    assert (outdir / "mapping_validation.md").exists()
    assert (outdir / "mapping_validation.csv").exists()
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()