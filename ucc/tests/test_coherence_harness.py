from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from ucc.core import run_module


def test_coherence_harness_build_and_run(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema_path = repo / "schema" / "ucc_module.schema.json"
    module_path = repo / "modules" / "coherence_audit.yml"

    md_path = repo / "notes" / "demo_writeup.md"
    assert md_path.exists()

    artifact_path = tmp_path / "coherence_from_demo_writeup.json"
    outdir = tmp_path / "coherence_out"

    # 1) Build artifact JSON via the CLI module (same interpreter)
    cmd = [
        sys.executable,
        "-m",
        "ucc.make_coherence_artifact",
        "--out",
        str(artifact_path),
        "--id",
        "ci-demo-writeup-001",
        "--domain",
        "research",
        "--question",
        "Demonstrate coherence_audit on a small writeup (CI).",
        "--answer_md",
        str(md_path),
        "--evidence_link",
        "https://github.com/pdxvoiceteacher/CoherenceLattice",
        "--reporting_primary",
        "github issues",
        "--reporting_escalation",
        "maintainers",
    ]
    subprocess.run(cmd, check=True)

    assert artifact_path.exists()
    data = json.loads(artifact_path.read_text(encoding="utf-8"))
    assert "coherence_artifact" in data

    # 2) Run the UCC module
    metrics, flags = run_module(module_path, artifact_path, outdir, schema_path)

    # 3) Assert outputs exist
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()
    assert (outdir / "coherence_audit.json").exists()
    assert (outdir / "coherence_audit.md").exists()
    assert (outdir / "coherence_claims.csv").exists()

    # CI-safe: just ensure flag exists (do not require pass/fail thresholds here)
    assert "overall_pass" in flags
