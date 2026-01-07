from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Optional


def newest_file(root: Path, filename: str) -> Optional[Path]:
    # Search repo for newest matching file; avoid common noise dirs
    bad_parts = {".git", ".venv", "__pycache__", ".pytest_cache"}
    hits = []
    for p in root.rglob(filename):
        if not p.is_file():
            continue
        if any(part in bad_parts for part in p.parts):
            continue
        hits.append(p)
    if not hits:
        return None
    hits.sort(key=lambda p: p.stat().st_mtime, reverse=True)
    return hits[0]


def main() -> int:
    ap = argparse.ArgumentParser(description="Anchor newest UCC audit_bundle.json into CoherenceLedger")
    ap.add_argument("--repo-root", default=None, help="Repo root (default: inferred)")
    ap.add_argument("--keystore", default=None, help="Keystore JSON path (default: .secrets/coherenceledger_keystore.json)")
    ap.add_argument("--ledger", default=None, help="Ledger JSONL path (default: ledger.jsonl)")
    ap.add_argument("--purpose", default="ucc.audit.anchor", help="Purpose string")
    ap.add_argument("--audit-bundle", default=None, help="Explicit audit_bundle.json path (default: newest in repo)")
    ap.add_argument("--report", default=None, help="Optional report.json path (default: sibling of audit_bundle.json if present)")
    ap.add_argument("--dry-run", action="store_true", help="Print what would be anchored, then exit")
    args = ap.parse_args()

    repo = Path(args.repo_root).resolve() if args.repo_root else Path(__file__).resolve().parents[2]
    keystore = Path(args.keystore).resolve() if args.keystore else repo / ".secrets" / "coherenceledger_keystore.json"
    ledger = Path(args.ledger).resolve() if args.ledger else repo / "ledger.jsonl"

    audit = Path(args.audit_bundle).resolve() if args.audit_bundle else newest_file(repo, "audit_bundle.json")
    if audit is None:
        print(f"ERROR: No audit_bundle.json found under {repo}", file=sys.stderr)
        return 2

    if args.report:
        report = Path(args.report).resolve()
    else:
        sibling = audit.parent / "report.json"
        report = sibling if sibling.exists() else None

    if not keystore.exists():
        print(f"ERROR: keystore not found: {keystore}", file=sys.stderr)
        print("Hint: run: python -m coherenceledger keygen --keystore <path>", file=sys.stderr)
        return 2

    if args.dry_run:
        print(f"repo={repo}")
        print(f"keystore={keystore}")
        print(f"ledger={ledger}")
        print(f"audit_bundle={audit}")
        print(f"report={report if report else '(none)'}")
        print(f"purpose={args.purpose}")
        return 0

    try:
        from coherenceledger.anchor import anchor_ucc_audit_bundle
    except Exception as e:
        print("ERROR: coherenceledger is not importable in this python env.", file=sys.stderr)
        print("Fix: pip install -e tools/coherenceledger_bootstrap", file=sys.stderr)
        raise

    res = anchor_ucc_audit_bundle(
        ledger_path=ledger,
        keystore_path=keystore,
        audit_bundle_path=audit,
        report_json_path=report,
        repo_root=repo,
        purpose=args.purpose,
    )

    print(f"event_id={res.event_id}")
    print(f"seal={res.seal}")
    print(f"ledger={res.ledger_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
