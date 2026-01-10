#!/usr/bin/env python3
from __future__ import annotations
import argparse, json
from pathlib import Path
from jsonschema import Draft202012Validator

REPO = Path(__file__).resolve().parents[2]
SCHEMA = REPO / "schema" / "telemetry" / "change_patch_plan.schema.json"

def load(p: Path):
    return json.loads(p.read_text(encoding="utf-8-sig"))

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("patch_plan_json")
    args = ap.parse_args()

    schema = load(SCHEMA)
    inst = load(Path(args.patch_plan_json))
    v = Draft202012Validator(schema)
    errs = sorted(v.iter_errors(inst), key=lambda e: e.path)
    if errs:
        print("[validate_patch_plan] FAIL")
        for e in errs[:120]:
            print(" -", list(e.path), e.message)
        return 2
    print("[validate_patch_plan] OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
