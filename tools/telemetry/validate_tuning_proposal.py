from __future__ import annotations

import argparse
import json
from pathlib import Path

from jsonschema import Draft202012Validator


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("proposal_json", help="Proposal JSON file")
    ap.add_argument("--schema", default="schema/plasticity_tuning_proposal.schema.json", help="Schema path")
    args = ap.parse_args()

    schema = json.loads(Path(args.schema).read_text(encoding="utf-8"))
    doc = json.loads(Path(args.proposal_json).read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(doc)
    print("[validate_tuning_proposal] OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
