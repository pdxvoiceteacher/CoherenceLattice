#!/usr/bin/env python3
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path

from jsonschema import Draft202012Validator

REPO = Path(__file__).resolve().parents[1]

def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))

def validate(schema_path: Path, instance_path: Path) -> list[str]:
    schema = load_json(schema_path)
    inst = load_json(instance_path)
    v = Draft202012Validator(schema)
    errs = sorted(v.iter_errors(inst), key=lambda e: e.path)
    out = []
    for e in errs:
        loc = "$"
        for p in e.path:
            loc += f".{p}" if isinstance(p, str) else f"[{p}]"
        out.append(f"{instance_path}: {loc}: {e.message}")
    return out

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true", help="Fail if expected governance files are missing")
    args = ap.parse_args()

    schema_dir = REPO / "schema" / "governance"
    gov_dir = REPO / "governance"

    # Schemas (only validate what exists)
    risk_schema = schema_dir / "risk_registry.schema.json"
    seal_schema = schema_dir / "audit_seal.schema.json"

    risk_registry = gov_dir / "risk" / "risk_registry.json"
    seals_dir = gov_dir / "seals"

    errors: list[str] = []

    def missing(path: Path, label: str):
        msg = f"Missing {label}: {path}"
        if args.strict:
            errors.append(msg)
        else:
            print("[validate_governance] WARN:", msg)

    # Risk registry validation
    risk_ids: set[str] = set()
    if risk_schema.exists():
        if risk_registry.exists():
            errors.extend(validate(risk_schema, risk_registry))
            reg = load_json(risk_registry)
            ids = [r.get("risk_id") for r in reg.get("risks", []) if isinstance(r, dict)]
            # uniqueness
            dupes = {x for x in ids if ids.count(x) > 1}
            if dupes:
                errors.append(f"{risk_registry}: duplicate risk_id(s): {sorted(dupes)}")
            risk_ids = {x for x in ids if isinstance(x, str)}
        else:
            missing(risk_registry, "risk registry")
    else:
        print("[validate_governance] INFO: risk_registry.schema.json not present; skipping risk registry validation")

    # Audit seal validation
    if seal_schema.exists():
        if seals_dir.exists():
            for p in seals_dir.rglob("*.json"):
                errors.extend(validate(seal_schema, p))
                # Optional cross-link: risk_dispositions risk_id must exist in registry if we have one
                if risk_ids:
                    seal = load_json(p)
                    for rd in seal.get("risk_dispositions", []) or []:
                        rid = rd.get("risk_id")
                        if isinstance(rid, str) and rid not in risk_ids:
                            errors.append(f"{p}: risk_dispositions references unknown risk_id: {rid}")
        else:
            missing(seals_dir, "seals directory")
    else:
        print("[validate_governance] INFO: audit_seal.schema.json not present; skipping audit seal validation")

    if errors:
        print("[validate_governance] FAIL")
        for e in errors[:200]:
            print("  -", e)
        if len(errors) > 200:
            print(f"  ... {len(errors)-200} more errors omitted")
        return 2

    print("[validate_governance] OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
