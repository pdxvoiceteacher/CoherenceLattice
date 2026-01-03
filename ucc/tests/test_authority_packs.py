from __future__ import annotations

from pathlib import Path
from ucc.core import run_module


CASES = [
    ("modules/authority_packs/nist_csf_profile_coverage.yml", "tasks/authority_packs/nist_csf_profile_sample.json"),
    ("modules/authority_packs/nist_ai_rmf_profile_coverage.yml", "tasks/authority_packs/nist_ai_rmf_profile_sample.json"),
    ("modules/authority_packs/iso27001_isms_profile_coverage.yml", "tasks/authority_packs/iso27001_isms_profile_sample.json"),
    ("modules/authority_packs/iso42001_aims_profile_coverage.yml", "tasks/authority_packs/iso42001_aims_profile_sample.json"),
    ("modules/authority_packs/iso31000_risk_profile_coverage.yml", "tasks/authority_packs/iso31000_risk_profile_sample.json"),
    ("modules/authority_packs/cobit_profile_coverage.yml", "tasks/authority_packs/cobit_profile_sample.json"),
    ("modules/authority_packs/cis_controls_profile_coverage.yml", "tasks/authority_packs/cis_controls_profile_sample.json"),
    ("modules/authority_packs/owasp_asvs_profile_coverage.yml", "tasks/authority_packs/owasp_asvs_profile_sample.json"),
    ("modules/authority_packs/soc2_mapping_profile_coverage.yml", "tasks/authority_packs/soc2_mapping_profile_sample.json"),
]


def test_authority_packs(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema_path = repo / "schema" / "ucc_module.schema.json"

    for mod_rel, task_rel in CASES:
        module_path = repo / mod_rel
        input_path = repo / task_rel
        outdir = tmp_path / (module_path.stem + "_out")
        metrics, flags = run_module(module_path, input_path, outdir, schema_path)
        assert flags["sections_complete"] is True
        assert flags.get("authority_deep_validation_ok", False) is True
        assert (outdir / "report.json").exists()
        assert (outdir / "audit_bundle.json").exists()