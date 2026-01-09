#!/usr/bin/env python3
from __future__ import annotations
import argparse
import json
from pathlib import Path
from jsonschema import Draft202012Validator

def load(p: Path):
    return json.loads(p.read_text(encoding="utf-8-sig"))

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--schema", required=True)
    ap.add_argument("--instance", required=True)
    args = ap.parse_args()

    schema = load(Path(args.schema))
    inst = load(Path(args.instance))

    v = Draft202012Validator(schema)
    errs = sorted(v.iter_errors(inst), key=lambda e: e.path)
    if errs:
        print("[validate_json] FAIL")
        for e in errs[:80]:
            print(" -", list(e.path), e.message)
        return 2

    print("[validate_json] OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
