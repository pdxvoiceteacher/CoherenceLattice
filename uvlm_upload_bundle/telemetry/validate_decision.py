#!/usr/bin/env python3
from __future__ import annotations
import argparse, json
from pathlib import Path
from jsonschema import Draft202012Validator

REPO = Path(__file__).resolve().parents[2]
SCHEMA = REPO / "schema" / "telemetry" / "control_decision.schema.json"

def load(p: Path):
    return json.loads(p.read_text(encoding="utf-8-sig"))

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("decision_json")
    args = ap.parse_args()

    schema = load(SCHEMA)
    data = load(Path(args.decision_json))
    v = Draft202012Validator(schema)
    errors = sorted(v.iter_errors(data), key=lambda e: e.path)
    if errors:
        print("[validate_decision] FAIL")
        for e in errors[:120]:
            print(" -", list(e.path), e.message)
        return 2
    print("[validate_decision] OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
