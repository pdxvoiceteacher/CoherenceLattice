from __future__ import annotations

import argparse
import json
from pathlib import Path

from ucc.vote_manifest import build_vote_manifest, write_vote_manifest_env


def load_json_dict(arg_value: str, file_value: str | None, label: str) -> dict:
    """
    Accepts:
      - JSON string: {"k":"v"}
      - @file.json  : reads JSON object from file
      - --*-file path.json : reads JSON object from file
    """
    if file_value:
        p = Path(file_value)
        return json.loads(p.read_text(encoding="utf-8"))

    s = (arg_value or "").strip()
    if s.startswith("@"):
        p = Path(s[1:])
        return json.loads(p.read_text(encoding="utf-8"))

    try:
        return json.loads(s) if s else {}
    except json.JSONDecodeError as e:
        raise SystemExit(
            f"\nERROR: Invalid JSON for {label}.\n"
            f"Received: {s}\n\n"
            f"Fix options:\n"
            f"  1) PowerShell: wrap JSON in single quotes:\n"
            f"     --{label} '{{\"key\":\"value\"}}'\n"
            f"  2) Use a file:\n"
            f"     --{label}-file path\\to\\{label}.json\n"
            f"  3) Or use @file syntax:\n"
            f"     --{label} @path\\to\\{label}.json\n"
        ) from e


def main() -> int:
    ap = argparse.ArgumentParser(description="Create Vote Manifest v0 (purpose-bound) and optionally sign+anchor")
    ap.add_argument("--outdir", required=True, help="Output directory for vote_manifest.json")
    ap.add_argument("--title", required=True)
    ap.add_argument("--purpose-id", required=True)
    ap.add_argument("--purpose-statement", required=True)
    ap.add_argument("--scope", required=True, help="e.g. org.governance | dao.governance | public.deliberation")
    ap.add_argument("--electorate-type", default="did_vc", help="did_vc | token_holders | manual_list")
    ap.add_argument("--anonymity", default="open", help="open | pseudonymous | secret")
    ap.add_argument("--tally", default="plaintext", help="plaintext | encrypted | zk")
    ap.add_argument("--anti-coercion", action="store_true")
    ap.add_argument("--weighting", default="one_person_one_vote", help="one_person_one_vote | token | coherence | quadratic")

    ap.add_argument("--electorate-rules", default="{}", help="JSON dict string, or @file.json")
    ap.add_argument("--electorate-rules-file", default=None, help="Path to JSON file")
    ap.add_argument("--weighting-params", default="{}", help="JSON dict string, or @file.json")
    ap.add_argument("--weighting-params-file", default=None, help="Path to JSON file")

    args = ap.parse_args()

    electorate_rules = load_json_dict(args.electorate_rules, args.electorate_rules_file, "electorate-rules")
    weighting_params = load_json_dict(args.weighting_params, args.weighting_params_file, "weighting-params")

    manifest = build_vote_manifest(
        title=args.title,
        purpose_id=args.purpose_id,
        purpose_statement=args.purpose_statement,
        scope=args.scope,
        electorate_type=args.electorate_type,
        electorate_rules=electorate_rules,
        anonymity_mode=args.anonymity,
        tally_mode=args.tally,
        anti_coercion=args.anti_coercion,
        weighting_mode=args.weighting,
        weighting_params=weighting_params,
    )

    outdir = Path(args.outdir)
    path = write_vote_manifest_env(outdir=outdir, manifest=manifest)

    print(f"Wrote: {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
