from __future__ import annotations

from pathlib import Path
import json

from ucc.core import run_module

def test_compare_sample(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    module_path = repo / "modules" / "tches_compare.yml"
    schema_path = repo / "schema" / "ucc_module.schema.json"
    input_path = repo / "tasks" / "tches_compare_sample.json"

    outdir = tmp_path / "out"
    metrics, flags = run_module(module_path, input_path, outdir, schema_path)

    assert "delta_warn_LambdaT_steps" in metrics
    assert (outdir / "comparison.md").exists()
    assert (outdir / "comparison.json").exists()
    assert (outdir / "audit_bundle.json").exists()
    assert flags["improved_warn_time"] in (True, False)

    bundle = json.loads((outdir / "audit_bundle.json").read_text(encoding="utf-8"))
    assert "comparison.md" in bundle["outputs"]