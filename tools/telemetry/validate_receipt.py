#!/usr/bin/env python3
from __future__ import annotations
import argparse, json
from pathlib import Path
from jsonschema import Draft202012Validator

REPO = Path(__file__).resolve().parents[2]
SCHEMA = REPO / "schema" / "telemetry" / "implementation_receipt.schema.json"

def load(p: Path):
    return json.loads(p.read_text(encoding="utf-8-sig"))

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("receipt_json", nargs="+")
    args = ap.parse_args()

    schema = load(SCHEMA)
    v = Draft202012Validator(schema)

    failed = False
    for path_str in args.receipt_json:
        p = Path(path_str)
        inst = load(p)
        errs = sorted(v.iter_errors(inst), key=lambda e: e.path)
        if errs:
            print(f"[validate_receipt] FAIL {p}")
            for e in errs[:80]:
                print(" -", list(e.path), e.message)
            failed = True

    if failed:
        return 2

    print("[validate_receipt] OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
