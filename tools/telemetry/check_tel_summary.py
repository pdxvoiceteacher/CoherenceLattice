from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict

from konomi.tel.build import build_tel_for_out_dir

REQUIRED_KEYS = [
    "schema",
    "tel_schema",
    "graph_id",
    "fingerprint_sha256",
    "nodes_total",
    "edges_total",
    "nodes_by_band",
    "edges_by_kind",
]

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out/telemetry_smoke", help="Run output directory (contains telemetry.json + stage dirs)")
    ap.add_argument("--telemetry", default="", help="Optional telemetry.json path (defaults to <out-dir>/telemetry.json)")
    ap.add_argument("--max-depth", type=int, default=2, help="Depth for shallow telemetry ingestion")
    args = ap.parse_args()

    out_dir = Path(args.out_dir)
    telemetry_path = Path(args.telemetry) if args.telemetry else (out_dir / "telemetry.json")

    data: Dict[str, Any] = json.loads(telemetry_path.read_text(encoding="utf-8"))
    tel = build_tel_for_out_dir(out_dir, data, max_depth=args.max_depth)
    s = tel.summary()

    missing = [k for k in REQUIRED_KEYS if k not in s]
    if missing:
        raise SystemExit(f"[tel_summary] FAIL missing keys: {missing}")

    nodes_total = s.get("nodes_total")
    edges_total = s.get("edges_total")
    if not isinstance(nodes_total, int) or nodes_total <= 0:
        raise SystemExit(f"[tel_summary] FAIL nodes_total invalid: {nodes_total}")
    if not isinstance(edges_total, int) or edges_total < 0:
        raise SystemExit(f"[tel_summary] FAIL edges_total invalid: {edges_total}")

    bands = s.get("nodes_by_band")
    if not isinstance(bands, dict):
        raise SystemExit(f"[tel_summary] FAIL nodes_by_band not dict: {type(bands)}")
    for b in ("STM", "MTM", "LTM"):
        if b not in bands:
            raise SystemExit(f"[tel_summary] FAIL missing band {b}")

    print(f"[tel_summary] OK nodes_total={nodes_total} edges_total={edges_total}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
