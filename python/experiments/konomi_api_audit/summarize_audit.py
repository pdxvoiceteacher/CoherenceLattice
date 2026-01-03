from __future__ import annotations

import argparse
import json
import platform
import subprocess
from collections import Counter
from pathlib import Path

import numpy as np


def get_git_commit() -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], stderr=subprocess.DEVNULL).decode().strip()
    except Exception:
        return "unknown"


def pct(xs, q):
    xs = sorted(xs)
    if not xs:
        return float("nan")
    k = int(round((q / 100.0) * (len(xs) - 1)))
    return xs[max(0, min(len(xs)-1, k))]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--infile", type=str, required=True, help="audit.jsonl")
    ap.add_argument("--outfile", type=str, required=True, help="summary.json")
    args = ap.parse_args()

    in_path = Path(args.infile)
    events = []
    for line in in_path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            events.append(json.loads(line))

    by_path = Counter(e.get("path","") for e in events)
    by_status = Counter(int(e.get("status",0)) for e in events)
    durs = [float(e.get("duration_ms", 0.0)) for e in events if e.get("duration_ms") is not None]
    callers = set(e.get("api_key_hash","") for e in events if e.get("api_key_hash",""))

    summary = {
        "api_audit_summary": {
            "git_commit": get_git_commit(),
            "source_log": str(in_path),
            "events": len(events),
            "by_path": dict(by_path),
            "by_status": dict(by_status),
            "p95_latency_ms": pct(durs, 95),
            "error_rate": float(sum(1 for e in events if int(e.get("status",0)) >= 500) / max(len(events),1)),
            "unique_callers": len(callers),
            "notes": "Summary derived from KONOMI API audit.jsonl (JSONL).",
        }
    }

    out_path = Path(args.outfile)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"Wrote: {out_path.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())