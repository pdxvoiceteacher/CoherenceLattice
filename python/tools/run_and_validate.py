from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Optional

RUN_ID_RE = re.compile(r"^run_id=([0-9a-f]{12})\s*$", re.IGNORECASE)

def repo_root() -> Path:
    return Path(__file__).resolve().parents[2]

def stream_run_wrapper(py: str) -> str:
    rr = repo_root()
    cmd = [py, "-u", str(rr / "python" / "tools" / "run_wrapper.py")]
    p = subprocess.Popen(cmd, cwd=str(rr), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    assert p.stdout is not None

    run_id: Optional[str] = None
    for line in p.stdout:
        line = line.rstrip("\n")
        print(line, flush=True)
        m = RUN_ID_RE.match(line.strip())
        if m:
            run_id = m.group(1)

    rc = p.wait()
    if rc != 0:
        raise SystemExit(rc)
    if not run_id:
        raise SystemExit("run_wrapper did not print run_id=<12-hex>")
    return run_id

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--python", default=sys.executable, help="Python executable to use (recommend venv python)")
    args = ap.parse_args()

    py = args.python
    rid = stream_run_wrapper(py)

    rr = repo_root()
    run_dir = rr / "paper" / "out" / "runs" / rid

    # Validate
    cmd = [py, str(rr / "python" / "tools" / "validate_run.py"), str(run_dir)]
    rc = subprocess.call(cmd, cwd=str(rr))
    if rc != 0:
        raise SystemExit(rc)

    print(f"RUN_ID={rid}", flush=True)  # CI-friendly
    return 0

if __name__ == "__main__":
    raise SystemExit(main())