from __future__ import annotations

from pathlib import Path
from ucc.core import run_module

def test_authority_pack_nist_sp800_171(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"
    module_path = repo / "modules" / "authority_nist_sp800_171_profile_coverage.yml"
    input_path  = repo / "tasks" / "authority_packs" / "nist_sp800_171_profile_task.json"
    outdir = tmp_path / "nist_sp800_171_out"
    metrics, flags = run_module(module_path, input_path, outdir, schema)
    assert flags.get("authority_deep_validation_ok") is True
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()
    assert (outdir / "authority_profile_checklist.md").exists()