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

from konomi.femto.model import FemtoModel


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


async def run_load(model: FemtoModel, n_requests: int, concurrency: int) -> dict:
    lat_ms = []
    loop = asyncio.get_running_loop()

    lag_samples = []
    stop = False

    async def lag_probe():
        nonlocal stop
        target = loop.time()
        while not stop:
            target += 0.01
            await asyncio.sleep(0.01)
            lag_samples.append(loop.time() - target)

    probe_task = asyncio.create_task(lag_probe())

    tracemalloc.start()
    start_cur, _ = tracemalloc.get_traced_memory()

    sem = asyncio.Semaphore(concurrency)

    async def one_call(i: int) -> float:
        async with sem:
            payload = f"req:{i}"
            t0 = time.perf_counter_ns()
            _ = await model.process(payload)
            t1 = time.perf_counter_ns()
            return (t1 - t0) / 1e6

    t_start = time.perf_counter()
    for i0 in range(0, n_requests, concurrency):
        batch = min(concurrency, n_requests - i0)
        tasks = [asyncio.create_task(one_call(i0 + j)) for j in range(batch)]
        lat_ms.extend(await asyncio.gather(*tasks))
    t_end = time.perf_counter()

    stop = True
    await asyncio.sleep(0)
    probe_task.cancel()
    try:
        await probe_task
    except asyncio.CancelledError:
        pass
    except Exception:
        pass

    end_cur, end_peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    elapsed_s = max(t_end - t_start, 1e-9)
    return {
        "concurrency": concurrency,
        "n_requests": n_requests,
        "p50_ms": pct(lat_ms, 50),
        "p95_ms": pct(lat_ms, 95),
        "mean_ms": float(sum(lat_ms) / len(lat_ms)),
        "throughput_rps": float(n_requests / elapsed_s),
        "max_loop_lag_ms": float(max(lag_samples) * 1e3) if lag_samples else float("nan"),
        "alloc_cur_kb_delta": float((end_cur - start_cur) / 1024.0),
        "alloc_peak_kb": float(end_peak / 1024.0),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", type=str, default="python/experiments/konomi_femto/out")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--n_requests", type=int, default=2000)
    ap.add_argument("--concurrency", type=str, default="1,9,64")
    ap.add_argument("--warmup", type=int, default=50)
    args = ap.parse_args()

    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    model = FemtoModel(dim=16, seed=args.seed)

    async def warm():
        for i in range(args.warmup):
            await model.process(f"warm:{i}")
    asyncio.run(warm())

    concs = [int(x.strip()) for x in args.concurrency.split(",") if x.strip()]

    rows = []
    for c in concs:
        rows.append(asyncio.run(run_load(model, args.n_requests, c)))

    csv_path = outdir / "femto_async_results.csv"
    with csv_path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        for r in rows:
            w.writerow(r)

    summary = {
        "femto_bench": {
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
                "warmup": args.warmup,
                "seed": args.seed,
            },
            "results_csv": str(csv_path),
            "results": rows,
            "gates": {},
            "notes": "FemtoModel is a stub for wiring + concurrency (not trained unless stated)."
        }
    }

    json_path = outdir / "femto_async_summary.json"
    json_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")

    print(f"Wrote: {csv_path.resolve()}")
    print(f"Wrote: {json_path.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
