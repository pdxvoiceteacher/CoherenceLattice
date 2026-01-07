from __future__ import annotations

import argparse
from pathlib import Path

from ucc.vote_tally import write_tally_env
from ucc.vote_guardrail import ensure_guardrail_passed


def main() -> int:
    ap = argparse.ArgumentParser(description="Tally v0 for Vote Manifest + Ballots (guardrail-gated)")
    ap.add_argument("--outdir", required=True, help="Vote run directory (contains ballots/)")
    ap.add_argument("--manifest", required=True, help="Path to vote_manifest.json")
    ap.add_argument("--verify-ballot-sigs", action="store_true", help="Verify DID signatures on ballots (open only)")
    ap.add_argument("--no-guardrail-cache", action="store_true", help="Force re-audit guardrail (ignore cached pass)")
    args = ap.parse_args()

    outdir = Path(args.outdir)
    manifest_path = Path(args.manifest)

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

    tally_path = write_tally_env(
        outdir=outdir,
        manifest_path=manifest_path,
        verify_ballot_signatures=args.verify_ballot_sigs,
    )
    print(f"Wrote: {tally_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
