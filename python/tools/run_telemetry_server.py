from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path

def main() -> int:
    repo_root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(repo_root / "python" / "src"))

    ap = argparse.ArgumentParser()
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=8009)
    ap.add_argument("--runs-root", default="", help="Override paper/out/runs directory")
    args = ap.parse_args()

    if args.runs_root:
        os.environ["COHERENCE_RUNS_ROOT"] = args.runs_root

    import uvicorn
    from coherence_telemetry_live.server import app

    uvicorn.run(app, host=args.host, port=args.port, log_level="info")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())