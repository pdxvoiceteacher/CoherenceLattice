from __future__ import annotations
from pathlib import Path
from ucc.core import run_module

def test_mapping_registry_check(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"
    module_path = repo / "modules" / "mapping_registry_check.yml"
    input_path = repo / "authorities" / "mappings" / "index.json"
    outdir = tmp_path / "mapping_registry_out"
    metrics, flags = run_module(module_path, input_path, outdir, schema)
    assert flags.get("mapping_index_ok") is True
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()