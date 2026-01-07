from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, Optional

from .hashing import sha256_hex
from . import jcs


def _sha256_file(path: Path) -> str:
    return sha256_hex(path.read_bytes())


def _safe_relpath(path: Path, base: Optional[Path]) -> str:
    try:
        return str(path.relative_to(base)) if base else str(path)
    except Exception:
        return str(path)


def build_ucc_anchor_payload(
    *,
    audit_bundle_path: Path,
    repo_root: Optional[Path] = None,
    report_json_path: Optional[Path] = None,
) -> Dict[str, Any]:
    """Build a small payload that anchors a UCC audit bundle.

    UCC audit bundles bind run results to inputs, environment, and git commit via hashes (per repo docs).
    We store only minimal, non-sensitive metadata + strong hashes.
    """
    audit_bundle_path = audit_bundle_path.resolve()
    payload: Dict[str, Any] = {
        "artifact_type": "ucc.audit_bundle",
        "audit_bundle_path": _safe_relpath(audit_bundle_path, repo_root),
        "audit_bundle_sha256": _sha256_file(audit_bundle_path),
    }

    try:
        bundle = json.loads(audit_bundle_path.read_text(encoding="utf-8"))
        # Try common keys without assuming an exact schema
        for k in ("git_commit", "git", "commit", "commit_sha", "commit_hash"):
            if k in bundle and isinstance(bundle[k], str):
                payload["git_commit"] = bundle[k]
                break
        # If bundle carries its own hash table, keep a hash of that table
        if "hashes" in bundle and isinstance(bundle["hashes"], dict):
            payload["hashes_sha256"] = sha256_hex(jcs.dumps(bundle["hashes"]).encode("utf-8"))
    except Exception:
        # If parsing fails, that's fine; we still anchor the file hash.
        pass

    if report_json_path:
        rp = report_json_path.resolve()
        payload["report_path"] = _safe_relpath(rp, repo_root)
        payload["report_sha256"] = _sha256_file(rp)
        try:
            report = json.loads(rp.read_text(encoding="utf-8"))
            # Shallow extract of common coherence metrics keys
            cm = report.get("coherence_metrics") if isinstance(report, dict) else None
            if isinstance(cm, dict):
                # include only scalar values
                keep = {}
                for kk in ("Psi", "psi", "E", "T", "DeltaS", "Lambda", "Psi_min", "psi_min"):
                    if kk in cm and isinstance(cm[kk], (int, float, str)):
                        keep[kk] = cm[kk]
                if keep:
                    payload["coherence_metrics"] = keep
        except Exception:
            pass

    return payload
