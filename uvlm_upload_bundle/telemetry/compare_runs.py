#!/usr/bin/env python3
from __future__ import annotations
import argparse, json
from pathlib import Path

def load(p: Path):
    # utf-8-sig strips BOM if present
    return json.loads(p.read_text(encoding="utf-8-sig"))

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("baseline")
    ap.add_argument("candidate")
    ap.add_argument("--tol", type=float, default=0.02, help="Tolerance for metric diffs")
    args = ap.parse_args()

    base = load(Path(args.baseline))
    cand = load(Path(args.candidate))

    keys = ["E", "T", "Psi", "DeltaS", "Lambda", "Es"]
    failed = False

    for k in keys:
        b = float(base["metrics"][k])
        c = float(cand["metrics"][k])
        if k == "DeltaS":
            if abs(c - b) > args.tol:
                print(f"[compare_runs] FAIL {k}: baseline={b} candidate={c} (abs>{args.tol})")
                failed = True
        else:
            denom = max(1e-9, abs(b))
            rel = abs(c - b) / denom
            if rel > args.tol:
                print(f"[compare_runs] FAIL {k}: baseline={b} candidate={c} (rel={rel:.3f} > {args.tol})")
                failed = True

    if failed:
        return 2

    print("[compare_runs] OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
