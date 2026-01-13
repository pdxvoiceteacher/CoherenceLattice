#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path

from jsonschema import Draft202012Validator


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("telemetry_json", help="telemetry.json containing optional claims[]")
    ap.add_argument("--claims-schema", default="schema/claims.schema.json")
    ap.add_argument("--repo-root", default=".")
    args = ap.parse_args()

    repo = Path(args.repo_root).resolve()
    tele_path = Path(args.telemetry_json).resolve()
    doc = json.loads(tele_path.read_text(encoding="utf-8-sig"))
    claims = doc.get("claims", None)

    if claims is None:
        print("[validate_claims] OK (no claims present)")
        return 0

    schema = json.loads((repo / args.claims_schema).read_text(encoding="utf-8-sig"))
    Draft202012Validator(schema).validate(claims)

    # Unique IDs + evidence existence
    seen = set()
    for c in claims:
        cid = c["id"]
        if cid in seen:
            raise SystemExit(f"[validate_claims] FAIL duplicate claim id: {cid}")
        seen.add(cid)

            # Unique IDs + evidence existence
    seen = set()
    run_dir = tele_path.parent
    for c in claims:
        cid = c["id"]
        if cid in seen:
            raise SystemExit(f"[validate_claims] FAIL duplicate claim id: {cid}")
        seen.add(cid)

        for key in ("evidence", "counterevidence"):
            for p in c.get(key, []) or []:
                # Accept evidence paths relative to repo root OR run_dir (portable submissions)
                p_norm = str(p).replace("\\", "/")
                pp_repo = (repo / p_norm)
                pp_run = (run_dir / p_norm)
                if not pp_repo.exists() and not pp_run.exists():
                    raise SystemExit(f"[validate_claims] FAIL missing {key} path: {p_norm}")

    print(f"[validate_claims] OK claims={len(claims)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


