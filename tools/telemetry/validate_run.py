#!/usr/bin/env python3
from __future__ import annotations
import argparse, json
from pathlib import Path
from jsonschema import Draft202012Validator

REPO = Path(__file__).resolve().parents[2]
SCHEMA = REPO / "schema" / "telemetry" / "telemetry_run.schema.json"

def load(p: Path):
    # utf-8-sig strips BOM if present
    return json.loads(p.read_text(encoding="utf-8-sig"))

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("telemetry_json", help="Path to telemetry.json")
    args = ap.parse_args()

    schema = load(SCHEMA)
    data = load(Path(args.telemetry_json))

    v = Draft202012Validator(schema)
    errors = sorted(v.iter_errors(data), key=lambda e: e.path)
    if errors:
        print("[validate_run] FAIL schema")
        for e in errors[:80]:
            print(" -", list(e.path), e.message)
        return 2

    E = float(data["metrics"]["E"])
    T = float(data["metrics"]["T"])
    Psi = float(data["metrics"]["Psi"])
    if abs(Psi - (E * T)) > 1e-6:
        print(f"[validate_run] FAIL Psi != E*T (Psi={Psi}, E*T={E*T})")
        return 2

    if not data["flags"]["telemetry_ok"]:
        print("[validate_run] FAIL telemetry_ok=false")
        return 2

    print("[validate_run] OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
