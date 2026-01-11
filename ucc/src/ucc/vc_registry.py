from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional
import json

from ucc.vc_issuer import vc_sha256


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def load_registry(path: Path) -> Dict[str, Any]:
    if not path.exists():
        return {"schema_id":"ucc.identity.vc_registry.v0_1","version":1,"entries":[],"revocations":[]}
    return json.loads(path.read_text(encoding="utf-8-sig"))


def save_registry(path: Path, reg: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(reg, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")


def add_vc(reg: Dict[str, Any], vc: Dict[str, Any]) -> None:
    entries = reg.setdefault("entries", [])
    vid = vc["id"]
    sha = vc_sha256(vc)
    issuer = vc["issuer"]
    subject = (vc.get("credentialSubject") or {}).get("id", "")

    types = vc.get("type", [])
    entries.append({
        "vc_id": vid,
        "vc_sha256": sha,
        "issuer_did": issuer,
        "subject_did": subject,
        "types": list(types),
        "issued_at": vc.get("issuanceDate", _utc_now_iso())
    })


def revoke_vc(reg: Dict[str, Any], vc_id: str, reason: str) -> None:
    revs = reg.setdefault("revocations", [])
    revs.append({"vc_id": vc_id, "revoked_at": _utc_now_iso(), "reason": reason})


def is_revoked(reg: Dict[str, Any], vc_id: str) -> bool:
    return any(r.get("vc_id") == vc_id for r in reg.get("revocations", []))
