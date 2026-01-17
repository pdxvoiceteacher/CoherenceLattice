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

from konomi.evgpu.ops import matmul


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
    ap.add_argument("--outdir", type=str, default="python/experiments/konomi_evgpu/out")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--repeats", type=int, default=30)
    ap.add_argument("--warmup", type=int, default=5)
    ap.add_argument("--dtype", type=str, default="float32", choices=["float32", "float64"])
    ap.add_argument("--p95_target_ms_1024", type=float, default=-1.0, help="Set >=0 to enable a gate on 1024x1024 batch=1 p95")
    args = ap.parse_args()

    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    rng = np.random.default_rng(args.seed)
    dtype = np.float32 if args.dtype == "float32" else np.float64

    shapes = [(256, 256), (512, 512), (1024, 1024)]
    batches = [1, 16]

    rows = []
    # warmup + measure
    for (n, k) in shapes:
        for b in batches:
            a = rng.standard_normal((b, n, k), dtype=dtype)
            w = rng.standard_normal((b, k, n), dtype=dtype)

            # warmup
            for _ in range(args.warmup):
                _ = matmul(a, w)

            times_ms = []
            for _ in range(args.repeats):
                t0 = time.perf_counter_ns()
                _ = matmul(a, w)
                t1 = time.perf_counter_ns()
                times_ms.append((t1 - t0) / 1e6)

            rows.append({
                "shape": f"{n}x{k}x{n}",
                "batch": b,
                "repeats": args.repeats,
                "p50_ms": pct(times_ms, 50),
                "p95_ms": pct(times_ms, 95),
                "mean_ms": float(sum(times_ms) / len(times_ms)),
                "dtype": args.dtype,
            })

    # write CSV
    csv_path = outdir / "evgpu_matmul_results.csv"
    with csv_path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        for r in rows:
            w.writerow(r)

    # optional gate: 1024 batch=1 p95
    gate = {"enabled": args.p95_target_ms_1024 >= 0, "target_ms": args.p95_target_ms_1024, "pass": None}
    if gate["enabled"]:
        v = next(r for r in rows if r["shape"].startswith("1024x1024") and r["batch"] == 1)["p95_ms"]
        gate["pass"] = (v <= gate["target_ms"])

    summary = {
        "evgpu_bench": {
            "git_commit": get_git_commit(),
            "machine_profile": {
                "platform": platform.platform(),
                "python": platform.python_version(),
                "numpy": np.__version__,
                "cpu_count": os.cpu_count(),
                "processor": platform.processor(),
            },
            "workload_definition": {
                "shapes": ["256x256", "512x512", "1024x1024"],
                "batches": [1, 16],
                "repeats": args.repeats,
                "warmup": args.warmup,
                "dtype": args.dtype,
                "seed": args.seed,
            },
            "results_csv": str(csv_path),
            "gate_1024_p95": gate,
            "notes": "CPU-only NumPy/BLAS matmul microbench (KONOMI v0 eVGPU baseline)."
        }
    }

    json_path = outdir / "evgpu_matmul_summary.json"
    json_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")

    print(f"Wrote: {csv_path.resolve()}")
    print(f"Wrote: {json_path.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
