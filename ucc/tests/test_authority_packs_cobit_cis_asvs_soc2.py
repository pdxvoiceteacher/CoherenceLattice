from __future__ import annotations
from pathlib import Path
from ucc.core import run_module

CASES = [
    ("modules/authority_cobit2019_profile_coverage.yml", "tasks/authority_packs/cobit2019_profile_task.json"),
    ("modules/authority_cis_controls_v8_profile_coverage.yml", "tasks/authority_packs/cis_controls_v8_profile_task.json"),
    ("modules/authority_owasp_asvs4_profile_coverage.yml", "tasks/authority_packs/owasp_asvs4_profile_task.json"),
    ("modules/authority_soc2_tsc_profile_coverage.yml", "tasks/authority_packs/soc2_tsc_profile_task.json"),
]

def test_authority_packs_cobit_cis_asvs_soc2(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"
    for mod_rel, task_rel in CASES:
        module_path = repo / mod_rel
        input_path = repo / task_rel
        outdir = tmp_path / module_path.stem
        metrics, flags = run_module(module_path, input_path, outdir, schema)
        assert flags.get("authority_deep_validation_ok") is True
        assert (outdir / "report.json").exists()
        assert (outdir / "audit_bundle.json").exists()
        assert (outdir / "authority_profile_checklist.md").exists()