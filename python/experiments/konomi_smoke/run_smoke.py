from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
import time
from pathlib import Path


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def get_git_commit(root: Path) -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=str(root), stderr=subprocess.DEVNULL).decode().strip()
    except Exception:
        return "unknown"


def run(cmd: list[str], cwd: Path) -> None:
    subprocess.run(cmd, cwd=str(cwd), check=True)


def read_json(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8"))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--python", type=str, default="", help="Path to python interpreter (defaults to current)")
    ap.add_argument("--outdir", type=str, default="python/experiments/konomi_smoke/out")
    ap.add_argument("--quick", action="store_true", help="small workloads for CI")
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()

    # repo root: .../python/experiments/konomi_smoke/run_smoke.py
    root = Path(__file__).resolve().parents[3]
    outdir = (root / args.outdir).resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    py = args.python.strip() or sys.executable
    print("Using python:", py)

    # component outdirs
    evgpu_out = outdir / "evgpu"
    femto_out = outdir / "femto"
    block_out = outdir / "blockarray"
    cube_out = outdir / "cube"
    for d in (evgpu_out, femto_out, block_out, cube_out):
        d.mkdir(parents=True, exist_ok=True)

    # workload knobs (CI-safe)
    if args.quick:
        ev_repeats, ev_warmup = 5, 1
        femto_nreq, femto_warm = 300, 20
        block_pts = 20000
        cube_nreq = 1200
    else:
        ev_repeats, ev_warmup = 30, 5
        femto_nreq, femto_warm = 2000, 50
        block_pts = 200000
        cube_nreq = 5000

    # 1) eVGPU
    run([py, "python/experiments/konomi_evgpu/bench_matmul.py",
         "--outdir", str(evgpu_out),
         "--seed", str(args.seed),
         "--repeats", str(ev_repeats),
         "--warmup", str(ev_warmup)], cwd=root)
    ev_json = evgpu_out / "evgpu_matmul_summary.json"

    # 2) Femto
    run([py, "python/experiments/konomi_femto/bench_async.py",
         "--outdir", str(femto_out),
         "--seed", str(args.seed),
         "--n_requests", str(femto_nreq),
         "--warmup", str(femto_warm),
         "--concurrency", "1,9,64"], cwd=root)
    femto_json = femto_out / "femto_async_summary.json"

    # 3) BlockArray
    run([py, "python/experiments/konomi_blockarray/bench_blockarray.py",
         "--outdir", str(block_out),
         "--seed", str(args.seed),
         "--n_points", str(block_pts),
         "--chunk", "16"], cwd=root)
    block_json = block_out / "blockarray_summary.json"

    # 4) Cube
    run([py, "python/experiments/konomi_cube/bench_cube.py",
         "--outdir", str(cube_out),
         "--n_requests", str(cube_nreq),
         "--concurrency", "1,9,64"], cwd=root)
    cube_json = cube_out / "cube_summary.json"

    summary = {
        "konomi_smoke": {
            "git_commit": get_git_commit(root),
            "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "python": sys.version.split()[0],
            "platform": platform.platform(),
            "seed": args.seed,
            "quick": bool(args.quick),
            "evgpu": {"summary_json": str(ev_json), "sha256": sha256_file(ev_json)},
            "femto": {"summary_json": str(femto_json), "sha256": sha256_file(femto_json)},
            "blockarray": {"summary_json": str(block_json), "sha256": sha256_file(block_json)},
            "cube": {"summary_json": str(cube_json), "sha256": sha256_file(cube_json)},
            "notes": "KONOMI smoke run for CI: small workloads + metadata completeness (not a perf gate).",
        }
    }

    out_json = outdir / "konomi_smoke_summary.json"
    out_json.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"Wrote: {out_json.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())