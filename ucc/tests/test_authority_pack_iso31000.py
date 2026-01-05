from __future__ import annotations
from pathlib import Path
from ucc.core import run_module

def test_authority_pack_iso31000(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"
    module_path = repo / "modules" / "authority_iso31000_profile_coverage.yml"
    input_path  = repo / "tasks" / "authority_packs" / "iso31000_profile_task.json"
    outdir = tmp_path / "iso31000_out"
    metrics, flags = run_module(module_path, input_path, outdir, schema)
    assert flags.get("authority_deep_validation_ok") is True
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()
    assert (outdir / "authority_profile_checklist.md").exists()