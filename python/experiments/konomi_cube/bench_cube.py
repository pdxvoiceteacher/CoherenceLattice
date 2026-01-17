from __future__ import annotations

import argparse
import csv
import json
import os
import platform
import subprocess
import time
import tracemalloc
import asyncio
from pathlib import Path
import sys

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[3]
SRC_PATH = REPO_ROOT / "python" / "src"
if SRC_PATH.exists() and str(SRC_PATH) not in sys.path:
    sys.path.insert(0, str(SRC_PATH))

from konomi.cube.runtime import CubeRuntime


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


async def run_bench(n_requests: int, concurrency: int, n_nodes: int, max_inflight: int, queue_max: int, process_delay_s: float) -> dict:
    cube = CubeRuntime(n_nodes=n_nodes, max_inflight=max_inflight, queue_max=queue_max, process_delay_s=process_delay_s)
    await cube.start()

    sem = asyncio.Semaphore(concurrency)
    lat_ms = []

    tracemalloc.start()
    start_cur, _ = tracemalloc.get_traced_memory()

    async def one(i: int):
        async with sem:
            key = f"k{i % 97}"  # fixed keyspace to exercise routing deterministically
            payload = f"msg:{i}"
            t0 = time.perf_counter_ns()
            _ = await cube.send(key, payload)
            t1 = time.perf_counter_ns()
            lat_ms.append((t1 - t0) / 1e6)

    t_start = time.perf_counter()
    tasks = [asyncio.create_task(one(i)) for i in range(n_requests)]
    await asyncio.gather(*tasks)
    t_end = time.perf_counter()

    end_cur, end_peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    await cube.stop()

    elapsed_s = max(t_end - t_start, 1e-9)
    return {
        "n_nodes": n_nodes,
        "queue_max": queue_max,
        "max_inflight": max_inflight,
        "process_delay_s": process_delay_s,
        "concurrency": concurrency,
        "n_requests": n_requests,
        "p50_ms": pct(lat_ms, 50),
        "p95_ms": pct(lat_ms, 95),
        "mean_ms": float(sum(lat_ms) / len(lat_ms)),
        "throughput_rps": float(n_requests / elapsed_s),
        "alloc_cur_kb_delta": float((end_cur - start_cur) / 1024.0),
        "alloc_peak_kb": float(end_peak / 1024.0),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", type=str, default="python/experiments/konomi_cube/out")
    ap.add_argument("--n_requests", type=int, default=5000)
    ap.add_argument("--concurrency", type=str, default="1,9,64")
    ap.add_argument("--n_nodes", type=int, default=9)
    ap.add_argument("--queue_max", type=int, default=1024)
    ap.add_argument("--max_inflight", type=int, default=1024)
    ap.add_argument("--process_delay_s", type=float, default=0.0)
    args = ap.parse_args()

    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    concs = [int(x.strip()) for x in args.concurrency.split(",") if x.strip()]
    rows = []
    for c in concs:
        rows.append(asyncio.run(run_bench(args.n_requests, c, args.n_nodes, args.max_inflight, args.queue_max, args.process_delay_s)))

    csv_path = outdir / "cube_results.csv"
    with csv_path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        for r in rows:
            w.writerow(r)

    summary = {
        "cube_bench": {
            "git_commit": get_git_commit(),
            "machine_profile": {
                "platform": platform.platform(),
                "python": platform.python_version(),
                "numpy": np.__version__,
                "cpu_count": os.cpu_count(),
                "processor": platform.processor(),
            },
            "workload_definition": {
                "n_requests": args.n_requests,
                "concurrency": concs,
                "n_nodes": args.n_nodes,
                "queue_max": args.queue_max,
                "max_inflight": args.max_inflight,
                "process_delay_s": args.process_delay_s,
            },
            "results_csv": str(csv_path),
            "results": rows,
            "notes": "KONOMI Cube runtime toy: deterministic routing + bounded inflight + bounded queues (CPU-only)."
        }
    }

    json_path = outdir / "cube_summary.json"
    json_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")

    print(f"Wrote: {csv_path.resolve()}")
    print(f"Wrote: {json_path.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
