from __future__ import annotations
import json
from pathlib import Path
from jsonschema import Draft202012Validator

SCHEMA = Path("ucc/schemas/prover/prover_manifest_v2.schema.json")

def main() -> int:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", required=True)
    args = ap.parse_args()

    schema = json.loads(SCHEMA.read_text(encoding="utf-8-sig"))
    Draft202012Validator.check_schema(schema)
    v = Draft202012Validator(schema)

    doc = json.loads(Path(args.manifest).read_text(encoding="utf-8-sig"))
    errors = sorted(v.iter_errors(doc), key=lambda e: e.path)
    if errors:
        e0 = errors[0]
        loc = ".".join(str(x) for x in e0.path) if e0.path else "<root>"
        raise SystemExit(f"INVALID prover_manifest at {loc}: {e0.message}")

    print("OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
