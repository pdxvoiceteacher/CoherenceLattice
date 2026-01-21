#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict


def hash_payload(payload: Dict[str, Any]) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def append_anchor(ledger_path: Path, anchor: Dict[str, Any]) -> None:
    ledger_path.parent.mkdir(parents=True, exist_ok=True)
    with ledger_path.open("a", encoding="utf-8", newline="\n") as f:
        f.write(json.dumps(anchor, ensure_ascii=False, sort_keys=True) + "\n")


def anchor_report(report: Dict[str, Any], ledger_path: Path) -> str:
    payload = dict(report)
    payload.pop("blockchain_anchor_hash", None)
    anchor_hash = hash_payload(payload)
    anchor = {
        "hash": anchor_hash,
        "run_id": report.get("run_id"),
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "schema": report.get("schema"),
    }
    append_anchor(ledger_path, anchor)
    return anchor_hash


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--report", required=True)
    ap.add_argument("--ledger", default="runs/history/blockchain_anchors.jsonl")
    args = ap.parse_args()

    report_path = Path(args.report)
    ledger_path = Path(args.ledger)
    report = json.loads(report_path.read_text(encoding="utf-8"))
    anchor_hash = anchor_report(report, ledger_path)
    print(anchor_hash)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
