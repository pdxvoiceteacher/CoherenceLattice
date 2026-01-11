"""
Vote Registry v0 (Replay Protection)

Open ballots only:
- Enforces a maximum ballots-per-DID limit.
- In strict mode, default max is 1 unless a manifest explicitly relaxes it.

Secret/pseudonymous modes:
- No DID-based replay prevention here (later: nullifiers/ZK).

Cross-platform, BOM-tolerant reads.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Dict


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def ballot_did(ballot_path: Path) -> str | None:
    try:
        b = _read_json(ballot_path)
        sig = b.get("signature") or {}
        did = sig.get("did")
        return did if isinstance(did, str) and did else None
    except Exception:
        return None


def count_ballots_by_did(ballots_dir: Path) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    if not ballots_dir.exists():
        return counts
    for p in ballots_dir.glob("*.json"):
        did = ballot_did(p)
        if did:
            counts[did] = counts.get(did, 0) + 1
    return counts


def enforce_max_ballots_per_did(ballots_dir: Path, did: str, max_allowed: int) -> None:
    """
    Raises ValueError if did already has >= max_allowed ballots in ballots_dir.
    """
    if max_allowed <= 0:
        return
    counts = count_ballots_by_did(ballots_dir)
    existing = counts.get(did, 0)
    if existing >= max_allowed:
        raise ValueError(f"ballot limit reached for DID {did}: {existing} >= {max_allowed}")
