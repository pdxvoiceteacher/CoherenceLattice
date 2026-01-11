import json
from pathlib import Path

from konomi.tel.build import build_tel_for_out_dir


def _write(p: Path, obj):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")


def test_build_tel_for_out_dir_is_deterministic(tmp_path: Path):
    # create a minimal fake run output directory
    out_dir = tmp_path / "out"
    out_dir.mkdir()

    # stage dirs (order should be lexicographic)
    s1 = out_dir / "konomi_smoke_base" / "cube"
    s2 = out_dir / "ucc_cov_out"

    _write(s1 / "cube_summary.json", {"ok": True})
    _write(s2 / "audit_bundle.json", {"bundle": 1})

    telemetry = {"hello": "world", "coherence_metrics": {"Psi": 1.0}}

    t1 = build_tel_for_out_dir(out_dir, telemetry, max_depth=1)
    t2 = build_tel_for_out_dir(out_dir, telemetry, max_depth=1)

    assert t1.to_json() == t2.to_json()

    # checkpoint labels stable
    doc = json.loads(t1.to_json())
    nodes = doc["nodes"]
    cps = [n for n in nodes if (n.get("payload") or {}).get("kind") == "checkpoint"]
    labels = [c["payload"]["label"] for c in cps]
    assert labels == [
        "run:telemetry_loaded",
        "step:konomi_smoke_base",
        "step:ucc_cov_out",
        "run:tel_built",
    ]
