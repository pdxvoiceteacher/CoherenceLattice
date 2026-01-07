from __future__ import annotations

import argparse
from pathlib import Path

from ucc.vote_ballot import build_ballot, load_manifest, write_ballot_env
from ucc.vote_guardrail import ensure_guardrail_passed


def main() -> int:
    ap = argparse.ArgumentParser(description="Cast Ballot v0 for a Vote Manifest v0 (guardrail-gated)")
    ap.add_argument("--manifest", required=True, help="Path to vote_manifest.json")
    ap.add_argument("--outdir", required=True, help="Vote run directory (same as manifest outdir)")
    ap.add_argument("--ballot-type", default="single_choice", help="single_choice | approval | ranked")
    ap.add_argument("--choice", required=True, help="For single_choice: a string option id/label")
    ap.add_argument("--title", default=None)
    ap.add_argument("--no-guardrail-cache", action="store_true", help="Force re-audit guardrail (ignore cached pass)")
    args = ap.parse_args()

    manifest_path = Path(args.manifest)
    outdir = Path(args.outdir)

    # Guardrail gate (strict follows COHERENCELEDGER_STRICT)
    import os
    strict = os.getenv("COHERENCELEDGER_STRICT","").lower() in {"1","true","yes"}
    ok = ensure_guardrail_passed(
        outdir=outdir,
        manifest_path=manifest_path,
        strict=strict,
        allow_cached=not args.no_guardrail_cache,
    )
    if not ok:
        raise SystemExit("Guardrail FAILED: vote manifest does not satisfy purpose policy.")

    manifest = load_manifest(manifest_path)
    manifest_id = manifest.get("manifest_id")
    if not manifest_id:
        raise SystemExit("manifest_id missing in manifest")

    if args.ballot_type == "single_choice":
        selection = {"choice": args.choice}
    elif args.ballot_type == "approval":
        selection = {"approve": [x.strip() for x in args.choice.split(",") if x.strip()]}
    elif args.ballot_type == "ranked":
        selection = {"rank": [x.strip() for x in args.choice.split(",") if x.strip()]}
    else:
        raise SystemExit(f"Unknown ballot-type: {args.ballot_type}")

    ballot = build_ballot(
        manifest_id=manifest_id,
        ballot_type=args.ballot_type,
        selection=selection,
        title=args.title,
    )

    path = write_ballot_env(outdir=outdir, ballot=ballot, manifest=manifest)
    print(f"Wrote: {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
