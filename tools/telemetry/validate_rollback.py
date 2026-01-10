#!/usr/bin/env python3
from __future__ import annotations
import argparse, json, glob
from pathlib import Path
from jsonschema import Draft202012Validator

REPO = Path(__file__).resolve().parents[2]
SCHEMA = REPO / "schema" / "telemetry" / "rollback_plan.schema.json"

def load(p: Path):
    return json.loads(p.read_text(encoding="utf-8-sig"))

def expand_args(args):
    out = []
    for a in args:
        if any(ch in a for ch in ["*", "?", "["]):
            matches = sorted(glob.glob(a))
            out.extend(matches)
        else:
            out.append(a)
    return out

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("rollback_json", nargs="+")
    ns = ap.parse_args()

    schema = load(SCHEMA)
    v = Draft202012Validator(schema)

    paths = expand_args(ns.rollback_json)
    if not paths:
        print("[validate_rollback] FAIL: no files matched")
        return 2

    failed = False
    for pstr in paths:
        p = Path(pstr)
        if not p.exists():
            print(f"[validate_rollback] FAIL missing: {p}")
            failed = True
            continue
        inst = load(p)
        errs = sorted(v.iter_errors(inst), key=lambda e: e.path)
        if errs:
            print(f"[validate_rollback] FAIL {p}")
            for e in errs[:80]:
                print(" -", list(e.path), e.message)
            failed = True

    if failed:
        return 2

    print("[validate_rollback] OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
