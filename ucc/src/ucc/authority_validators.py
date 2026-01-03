from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from typing import Any, Dict, List, Tuple, Optional


def _parse_iso_utc(s: str) -> Optional[datetime]:
    """
    Parse ISO8601 timestamps, allowing trailing 'Z'.
    Returns timezone-aware datetime or None if invalid.
    """
    if not isinstance(s, str) or not s.strip():
        return None
    s = s.strip()
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    try:
        dt = datetime.fromisoformat(s)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt
    except Exception:
        return None


def validate_authority_profile(
    doc: Dict[str, Any],
    sections_key: str,
    *,
    min_links: int = 1,
    require_review_dates: bool = True,
    require_exception_items: bool = True,
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    """
    Deeper validation for authority-pack artifacts:
    - evidence.links must exist and have length >= min_links
    - review_cycle.last_review_utc and next_review_utc must be parseable and ordered
    - exceptions.items entries must have issued_utc and expires_utc parseable and expires > issued
    """
    metrics: Dict[str, Any] = {}
    flags: Dict[str, Any] = {}

    section = doc.get(sections_key)
    if not isinstance(section, dict):
        metrics["authority_section_ok"] = False
        flags["authority_section_ok"] = False
        return metrics, flags

    # ---- Evidence links ----
    evidence = section.get("evidence", {})
    links = []
    if isinstance(evidence, dict):
        links = evidence.get("links", [])
    links_ok = isinstance(links, list) and len([x for x in links if isinstance(x, str) and x.strip()]) >= min_links
    metrics["evidence_links_count"] = int(len(links)) if isinstance(links, list) else 0
    metrics["evidence_links_min_required"] = int(min_links)
    flags["evidence_links_ok"] = bool(links_ok)

    # ---- Review dates ----
    review_ok = True
    last_dt = next_dt = None
    if require_review_dates:
        review = section.get("review_cycle", {})
        last_s = review.get("last_review_utc") if isinstance(review, dict) else None
        next_s = review.get("next_review_utc") if isinstance(review, dict) else None
        last_dt = _parse_iso_utc(last_s) if isinstance(last_s, str) else None
        next_dt = _parse_iso_utc(next_s) if isinstance(next_s, str) else None
        review_ok = (last_dt is not None) and (next_dt is not None) and (next_dt >= last_dt)

    metrics["review_dates_required"] = bool(require_review_dates)
    metrics["review_last_ok"] = bool(last_dt is not None) if require_review_dates else True
    metrics["review_next_ok"] = bool(next_dt is not None) if require_review_dates else True
    flags["review_dates_ok"] = bool(review_ok)

    # ---- Exception expiries ----
    exc_ok = True
    invalid_items = 0
    total_items = 0
    if require_exception_items:
        exc = section.get("exceptions", {})
        items = exc.get("items", []) if isinstance(exc, dict) else []
        if not isinstance(items, list):
            items = []
        total_items = len(items)
        for it in items:
            if not isinstance(it, dict):
                invalid_items += 1
                continue
            issued = it.get("issued_utc")
            expires = it.get("expires_utc")
            issued_dt = _parse_iso_utc(issued) if isinstance(issued, str) else None
            expires_dt = _parse_iso_utc(expires) if isinstance(expires, str) else None
            if issued_dt is None or expires_dt is None or not (expires_dt > issued_dt):
                invalid_items += 1
        exc_ok = (total_items > 0) and (invalid_items == 0)

    metrics["exceptions_required"] = bool(require_exception_items)
    metrics["exceptions_items_count"] = int(total_items)
    metrics["exceptions_items_invalid"] = int(invalid_items)
    flags["exceptions_expiry_ok"] = bool(exc_ok)

    # ---- Overall ----
    overall = bool(links_ok) and bool(review_ok) and bool(exc_ok)
    flags["authority_deep_validation_ok"] = overall

    return metrics, flags