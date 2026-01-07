from __future__ import annotations

import argparse
from pathlib import Path

from ucc.vote_guardrail import write_guardrail


def main() -> int:
    ap = argparse.ArgumentParser(description="Audit Vote Manifest against purpose-bound guardrail policy")
    ap.add_argument("--outdir", required=True, help="Vote run directory")
    ap.add_argument("--manifest", required=True, help="Path to vote_manifest.json")
    ap.add_argument("--strict", action="store_true", help="Strict mode (enforce extra constraints)")
    args = ap.parse_args()

    outdir = Path(args.outdir)
    manifest = Path(args.manifest)

    enable = (str(__import__("os").environ.get("COHERENCELEDGER_ENABLE","")).lower() in {"1","true","yes"})
    paths = write_guardrail(
        outdir=outdir,
        manifest_path=manifest,
        strict=args.strict,
        sign=enable,
        anchor=enable,
        ledger_purpose=__import__("os").environ.get("COHERENCELEDGER_PURPOSE","ucc.vote_guardrail.anchor"),
    )

    print(f"Wrote: {paths['report']}")
    print(f"Wrote: {paths['audit_bundle']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
