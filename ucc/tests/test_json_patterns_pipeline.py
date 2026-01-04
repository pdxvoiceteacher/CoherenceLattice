from __future__ import annotations

import json
from pathlib import Path

from ucc.core import run_module


def test_verify_json_patterns_pipeline(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema_path = repo / "schema" / "ucc_module.schema.json"

    # Local JSON with nested provenance-like fields
    src_json = tmp_path / "audit_bundle.json"
    src_json.write_text(
        json.dumps(
            {
                "bundle_version": "0.1",
                "environment": {"git_commit": "a" * 40},
                "module": {"sha256": "b" * 64},
                "input": {"sha256": "c" * 64},
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    task = {
        "coherence_artifact": {
            "id": "ci-json-patterns",
            "domain": "research",
            "question": "CI: verify regex patterns against cited JSON sources.",
            "answer": "CI scaffold.",
            "sections": {
                "assumptions": "Proxy audit.",
                "limitations": "CI scaffold.",
                "uncertainty": "CI scaffold.",
                "disclosure": "CI scaffold.",
            },
            "claims": [
                {
                    "id": "c1",
                    "text": "From audit_bundle.json: environment.git_commit ~ /^[0-9a]{40}$/; module.sha256 ~ /^[0-9b]{64}$/; input.sha256 ~ /^[0-9c]{64}$/; bundle_version ~ /^0\\.1$/ .",
                    "citations": ["s_audit"],
                }
            ],
            "sources": [{"id": "s_audit", "title": "audit_bundle.json", "url": f"local:{src_json}"}],
            "evidence": {"links": ["https://github.com/pdxvoiceteacher/CoherenceLattice"], "artifacts": []},
            "reporting_channel": {"primary": "github issues", "escalation": "maintainers"},
        }
    }

    input_json = tmp_path / "artifact.json"
    input_json.write_text(json.dumps(task, indent=2, sort_keys=True), encoding="utf-8")

    module_yml = tmp_path / "module.yml"
    module_yml.write_text(
        "\n".join(
            [
                'ucc_version: "0.1"',
                "module:",
                '  id: "test.verify_json_patterns"',
                '  version: "0.1.0"',
                '  title: "Test verify_json_patterns"',
                '  intent: "CI pipeline test"',
                "  authors:",
                '    - name: "CI"',
                "steps:",
                "  - type: ingest_json",
                "    id: ingest",
                "  - type: verify_json_patterns",
                "    id: p",
                "    params:",
                '      sections_key: "coherence_artifact"',
                "      require_any: true",
                "      fail_on_unresolved: true",
                '      name_json: "json_patterns.json"',
                '      name_md: "json_patterns.md"',
                "  - type: emit_report",
                "    id: report",
                "    params:",
                '      report_name: "report.json"',
                "",
            ]
        ),
        encoding="utf-8",
    )

    outdir = tmp_path / "out"
    metrics, flags = run_module(module_yml, input_json, outdir, schema_path)

    assert flags.get("json_patterns_ok") is True
    assert (outdir / "json_patterns.json").exists()
    assert (outdir / "json_patterns.md").exists()
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()
