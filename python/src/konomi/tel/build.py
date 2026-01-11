from __future__ import annotations

from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional

from .tel_graph import TelGraph
from .recorder import TelRecorder


def iter_stage_dirs(out_dir: Path) -> List[Path]:
    """Deterministic stage discovery: sorted, limited allowlist by prefix."""
    stage_dirs: List[Path] = []
    for p in sorted(out_dir.iterdir(), key=lambda x: x.name):
        if not p.is_dir():
            continue
        name = p.name
        if name.startswith("konomi_smoke_") or name.startswith("ucc_cov_"):
            stage_dirs.append(p)
    return stage_dirs


def build_tel_for_out_dir(out_dir: Path, telemetry_data: Dict[str, Any], *, max_depth: int = 2) -> TelGraph:
    """
    Deterministically build a TEL graph from an output directory + telemetry dict.

    - Adds run checkpoints
    - Adds a checkpoint per stage dir (sorted)
    - Attaches *_summary.json and audit_bundle.json files
    - Optionally ingests shallow telemetry tree for connectivity
    """
    tel = TelGraph(graph_id="tel_run_wrapper", meta={"source": "build_tel_for_out_dir"})
    rec = TelRecorder(tel)

    rec.checkpoint("run:telemetry_loaded", meta={"out_dir": str(out_dir)})

    stage_dirs = iter_stage_dirs(out_dir)
    for idx, stage in enumerate(stage_dirs):
        cp = rec.checkpoint(f"step:{stage.name}", meta={"dir": stage.name, "stage_index": idx})

        for f in sorted(stage.rglob("*_summary.json"), key=lambda x: x.as_posix()):
            rec.attach_file(cp, f, root=out_dir, kind="summary_json")

        for f in sorted(stage.rglob("audit_bundle.json"), key=lambda x: x.as_posix()):
            rec.attach_file(cp, f, root=out_dir, kind="audit_bundle")

    tel.ingest_json_tree(telemetry_data, root_id="telemetry", max_depth=max_depth)
    rec.checkpoint("run:tel_built")

    return tel
