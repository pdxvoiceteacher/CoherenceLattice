"""JSON Canonicalization helpers.

We use a pragmatic (not full RFC 8785) canonicalization:
- sort keys
- no insignificant whitespace
- UTF-8, ensure_ascii=False
- stable datetimes serialized to ISO-8601 strings

This is sufficient for an internal ledger + signatures, and keeps dependencies minimal.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from typing import Any


def _normalize(obj: Any) -> Any:
    if isinstance(obj, datetime):
        # Always ISO in UTC
        dt = obj.astimezone(timezone.utc)
        return dt.replace(microsecond=0).isoformat().replace("+00:00", "Z")
    if isinstance(obj, bytes):
        # bytes are not JSON; represent as hex
        return obj.hex()
    if isinstance(obj, (list, tuple)):
        return [_normalize(x) for x in obj]
    if isinstance(obj, dict):
        return {str(k): _normalize(v) for k, v in obj.items()}
    return obj


def dumps(obj: Any) -> str:
    """Return canonical JSON string."""
    normalized = _normalize(obj)
    return json.dumps(
        normalized,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    )


def loads(s: str) -> Any:
    return json.loads(s)
