#!/usr/bin/env python3
from __future__ import annotations
import argparse, subprocess, sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]

PROTECTED_PREFIXES = (
    "ucc/src/",
    "tools/telemetry/",
    "schema/telemetry/",
    ".github/workflows/",
)

RECEIPTS_GLOB = "governance/implementation/receipts/*.json"
ROLLBACKS_GLOB = "governance/implementation/rollback/*.json"

def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=str(REPO), text=True).strip()

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", required=True, help="e.g. origin/master")
    ap.add_argument("--head", default="HEAD")
    args = ap.parse_args()

    changed = git("diff", "--name-only", f"{args.base}...{args.head}").splitlines()
    changed = [c.strip() for c in changed if c.strip()]

    protected_changed = any(any(c.startswith(p) for p in PROTECTED_PREFIXES) for c in changed)
    if not protected_changed:
        print("[impl_gate] OK: no protected changes")
        return 0

    receipts = list(REPO.glob(RECEIPTS_GLOB))
    rollbacks = list(REPO.glob(ROLLBACKS_GLOB))

    if not receipts or not rollbacks:
        print("[impl_gate] FAIL: protected changes require receipt + rollback plan")
        print("Protected prefixes:", PROTECTED_PREFIXES)
        print("Receipts:", [p.as_posix() for p in receipts])
        print("Rollbacks:", [p.as_posix() for p in rollbacks])
        print("Changed files:")
        for c in changed:
            print(" -", c)
        return 2

    print("[impl_gate] OK: receipt+rollback present")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
