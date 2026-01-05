from __future__ import annotations
from pathlib import Path
from ucc.core import run_module

MAPPING_FILES = [
    "authorities/mappings/cis_controls_to_soc2_sample.csv",
    "authorities/mappings/asvs_to_top10_sample.csv",
    "authorities/mappings/cobit_to_iso31000_sample.csv",
    "authorities/mappings/cobit_to_nist_csf_sample.csv",
]

def test_mapping_tables_validate(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"
    module_path = repo / "modules" / "mapping_table_validate.yml"
    for rel in MAPPING_FILES:
        inp = repo / rel
        outdir = tmp_path / ("map_" + inp.stem)
        metrics, flags = run_module(module_path, inp, outdir, schema)
        assert flags.get("mapping_table_ok") is True
        assert (outdir / "mapping_validation.md").exists()
        assert (outdir / "mapping_validation.csv").exists()
        assert (outdir / "report.json").exists()
        assert (outdir / "audit_bundle.json").exists()