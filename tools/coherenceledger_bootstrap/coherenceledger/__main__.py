from __future__ import annotations

import argparse
from pathlib import Path
import sys

from .keystore import KeyStore
from .ledger import Ledger
from .anchor import anchor_ucc_audit_bundle


def _p(s: str) -> Path:
    return Path(s).expanduser().resolve()


def cmd_keygen(args: argparse.Namespace) -> int:
    ks = KeyStore(path=_p(args.keystore))
    did = ks.generate(overwrite=args.overwrite)
    print(did.did)
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    ledger = Ledger(path=_p(args.ledger))
    ledger.verify()
    print("OK")
    return 0


def cmd_anchor_ucc(args: argparse.Namespace) -> int:
    res = anchor_ucc_audit_bundle(
        ledger_path=_p(args.ledger),
        keystore_path=_p(args.keystore),
        audit_bundle_path=_p(args.audit_bundle),
        report_json_path=_p(args.report) if args.report else None,
        repo_root=_p(args.repo_root) if args.repo_root else None,
        purpose=args.purpose,
    )
    print(f"event_id={res.event_id}")
    print(f"seal={res.seal}")
    print(f"ledger={res.ledger_path}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="python -m coherenceledger", description="CoherenceLattice Ledger bootstrap tools")
    sub = p.add_subparsers(dest="cmd", required=True)

    p_key = sub.add_parser("keygen", help="Generate a new did:key keystore (Ed25519)")
    p_key.add_argument("--keystore", required=True, help="Path to keystore JSON")
    p_key.add_argument("--overwrite", action="store_true", help="Overwrite existing keystore file")
    p_key.set_defaults(func=cmd_keygen)

    p_ver = sub.add_parser("verify", help="Verify a ledger JSONL file (hash chain + signatures)")
    p_ver.add_argument("--ledger", required=True, help="Path to ledger.jsonl")
    p_ver.set_defaults(func=cmd_verify)

    p_anchor = sub.add_parser("anchor-ucc", help="Anchor a UCC audit_bundle.json into the ledger")
    p_anchor.add_argument("--ledger", required=True, help="Path to ledger.jsonl")
    p_anchor.add_argument("--keystore", required=True, help="Path to keystore JSON created by keygen")
    p_anchor.add_argument("--audit-bundle", required=True, help="Path to audit_bundle.json")
    p_anchor.add_argument("--report", help="Optional path to report.json to also hash + extract coherence_metrics")
    p_anchor.add_argument("--repo-root", help="Optional repo root to store relative paths in payload")
    p_anchor.add_argument("--purpose", default="ucc.audit.anchor", help="Purpose string (policy-bound meaning)")
    p_anchor.set_defaults(func=cmd_anchor_ucc)

    return p


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
