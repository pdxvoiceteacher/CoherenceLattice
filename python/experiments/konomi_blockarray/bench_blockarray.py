from __future__ import annotations

import argparse
import csv
import json
import os
import platform
import subprocess
import time
from pathlib import Path
import sys

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[3]
SRC_PATH = REPO_ROOT / "python" / "src"
if SRC_PATH.exists() and str(SRC_PATH) not in sys.path:
    sys.path.insert(0, str(SRC_PATH))

from konomi.blockarray.blockarray import BlockArray


def pct(xs, q):
    xs = sorted(xs)
    if not xs:
        return float("nan")
    k = int(round((q / 100.0) * (len(xs) - 1)))
    return xs[max(0, min(len(xs) - 1, k))]


def get_git_commit() -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], stderr=subprocess.DEVNULL).decode().strip()
    except Exception:
        return "unknown"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", type=str, default="python/experiments/konomi_blockarray/out")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--shape", type=str, default="1000,1000,1000")
    ap.add_argument("--chunk", type=int, default=16)
    ap.add_argument("--n_points", type=int, default=200000)
    ap.add_argument("--scan_box", type=str, default="0,256,0,256,0,256")
    ap.add_argument("--max_blocks", type=int, default=5000)
    ap.add_argument("--max_hits", type=int, default=20000)
    args = ap.parse_args()

    outdir = Path(args.outdir); outdir.mkdir(parents=True, exist_ok=True)
    sx, sy, sz = [int(x) for x in args.shape.split(",")]
    x0,x1,y0,y1,z0,z1 = [int(x) for x in args.scan_box.split(",")]

    rng = np.random.default_rng(args.seed)
    ba = BlockArray(shape=(sx,sy,sz), chunk=args.chunk)

    # Random sparse writes
    coords = np.column_stack([
        rng.integers(0, sx, size=args.n_points, dtype=np.int64),
        rng.integers(0, sy, size=args.n_points, dtype=np.int64),
        rng.integers(0, sz, size=args.n_points, dtype=np.int64),
    ])
    vals = rng.standard_normal(size=args.n_points).astype(np.float32)

    t0 = time.perf_counter()
    ba.set_many(coords, vals)
    t1 = time.perf_counter()

    write_s = t1 - t0
    blocks = len(ba.blocks)
    bytes_est = ba.estimate_bytes()

    # Bounded scan
    t2 = time.perf_counter()
    visited, hits, _items = ba.scan_bbox(x0,x1,y0,y1,z0,z1, max_blocks=args.max_blocks, max_hits=args.max_hits)
    t3 = time.perf_counter()
    scan_s = t3 - t2

    rows = [{
        "n_points": args.n_points,
        "shape": f"{sx}x{sy}x{sz}",
        "chunk": args.chunk,
        "blocks_allocated": blocks,
        "bytes_est": bytes_est,
        "write_s": write_s,
        "write_pts_per_s": float(args.n_points / max(write_s, 1e-9)),
        "scan_box": args.scan_box,
        "scan_s": scan_s,
        "scan_blocks_visited": visited,
        "scan_hits": hits,
        "max_blocks": args.max_blocks,
        "max_hits": args.max_hits,
    }]

    csv_path = outdir / "blockarray_results.csv"
    with csv_path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        for r in rows:
            w.writerow(r)

    summary = {
        "blockarray_bench": {
            "git_commit": get_git_commit(),
            "machine_profile": {
                "platform": platform.platform(),
                "python": platform.python_version(),
                "numpy": np.__version__,
                "cpu_count": os.cpu_count(),
                "processor": platform.processor(),
            },
            "workload_definition": {
                "shape": [sx,sy,sz],
                "chunk": args.chunk,
                "n_points": args.n_points,
                "scan_box": [x0,x1,y0,y1,z0,z1],
                "max_blocks": args.max_blocks,
                "max_hits": args.max_hits,
                "seed": args.seed,
            },
            "results_csv": str(csv_path),
            "results": rows,
            "notes": "Sparse chunked 3D BlockArray (allocate-on-write, bounded scan over allocated blocks)."
        }
    }

    json_path = outdir / "blockarray_summary.json"
    json_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")

    print(f"Wrote: {csv_path.resolve()}")
    print(f"Wrote: {json_path.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
