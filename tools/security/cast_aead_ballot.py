from __future__ import annotations

import argparse
from pathlib import Path

from ucc.vote_ballot_aead import build_aead_commit_and_reveal, write_aead_commit, write_aead_reveal
from ucc.vote_guardrail import ensure_guardrail_passed


def main() -> int:
    ap = argparse.ArgumentParser(description="Cast SECRET ballot v0.3 (AES-GCM commit + demo reveal)")
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--manifest-id", required=True)
    ap.add_argument("--choice", required=True)
    ap.add_argument("--reveal-now", action="store_true")
    args = ap.parse_args()

    outdir = Path(args.outdir)
    import os
    strict = os.getenv("COHERENCELEDGER_STRICT","").lower() in {"1","true","yes"}
    ok = ensure_guardrail_passed(outdir=outdir, manifest_path=outdir/"vote_manifest.json", strict=strict, allow_cached=True)
    if not ok:
        raise SystemExit("Guardrail FAILED.")

    commit, reveal = build_aead_commit_and_reveal(manifest_id=args.manifest_id, plaintext_choice=args.choice)
    cp = write_aead_commit(outdir=outdir, commit_doc=commit)
    print(f"Wrote commit: {cp}")

    if args.reveal_now:
        rp = write_aead_reveal(outdir=outdir, reveal_doc=reveal)
        print(f"Wrote reveal: {rp}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
