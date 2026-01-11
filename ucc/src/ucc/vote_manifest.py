"""
Vote Manifest v0 (purpose-bound governance object)

This manifest defines *what a vote is*, not the ballots themselves.

Design goals:
- Purpose-bound: rules are explicit and auditable.
- Deterministic: canonical JSON for signing.
- Modular: does nothing unless explicitly invoked.
- Optional security: DID signature + ledger anchoring when COHERENCELEDGER_ENABLE is truthy.
- Cross-platform: pathlib everywhere, no shell dependencies.

This does not implement ZK voting yet; it creates the "contract of intent"
that later ZK/anonymous ballots must conform to.
"""
from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional
from uuid import uuid4

import hashlib
import json
import os


# -------------------------
# Schema (v0)
# -------------------------
VOTE_MANIFEST_SCHEMA_ID = "ucc.vote_manifest.v0"

VOTE_MANIFEST_SCHEMA_V0: Dict[str, Any] = {
    "schema_id": VOTE_MANIFEST_SCHEMA_ID,
    "required": [
        "version",
        "manifest_id",
        "created_at",
        "purpose",
        "electorate",
        "anonymity",
        "weighting",
        "timeline",
    ],
    "purpose_required": ["id", "statement", "scope"],
    "electorate_required": ["type", "rules"],
    "anonymity_required": ["mode", "tally", "anti_coercion"],
    "weighting_required": ["mode", "params"],
    "timeline_required": ["opens_at", "closes_at", "timezone"],
}


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _truthy_env(name: str) -> bool:
    return os.getenv(name, "").strip().lower() in {"1", "true", "yes", "y", "on"}


def _canonical_dumps(obj: Any) -> str:
    """
    Deterministic JSON serialization.

    Prefer coherenceledger.jcs if installed; else fall back to stable json.dumps.
    """
    try:
        from coherenceledger import jcs  # type: ignore
        return jcs.dumps(obj)
    except Exception:
        return json.dumps(obj, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_hex(path.read_bytes())


def _safe_relpath(path: Path, base: Optional[Path]) -> str:
    try:
        return str(path.resolve().relative_to(base.resolve())) if base else str(path.resolve())
    except Exception:
        return str(path.resolve())


def schema_sha256() -> str:
    return _sha256_hex(_canonical_dumps(VOTE_MANIFEST_SCHEMA_V0).encode("utf-8"))


def build_vote_manifest(
    *,
    title: str,
    purpose_id: str,
    purpose_statement: str,
    scope: str,
    electorate_type: str = "did_vc",
    electorate_rules: Optional[Dict[str, Any]] = None,
    anonymity_mode: str = "open",   # open | pseudonymous | secret
    tally_mode: str = "plaintext",  # plaintext | encrypted | zk
    anti_coercion: bool = False,
    weighting_mode: str = "one_person_one_vote",  # one_person_one_vote | token | coherence | quadratic
    weighting_params: Optional[Dict[str, Any]] = None,
    opens_at: Optional[str] = None,
    closes_at: Optional[str] = None,
    timezone: str = "UTC",
    proof_policy: Optional[Dict[str, Any]] = None,
    extra: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    electorate_rules = electorate_rules or {}
    weighting_params = weighting_params or {}
    opens_at = opens_at or _utc_now_iso()
    closes_at = closes_at or _utc_now_iso()

    manifest: Dict[str, Any] = {
        "version": 1,
        "schema_id": VOTE_MANIFEST_SCHEMA_ID,
        "schema_sha256": schema_sha256(),
        "manifest_id": str(uuid4()),
        "created_at": _utc_now_iso(),
        "title": title,
        "purpose": {
            "id": purpose_id,
            "statement": purpose_statement,
            "scope": scope,
            "audit_required": True,
        },
        "electorate": {
            "type": electorate_type,
            "rules": electorate_rules,
        },
        "anonymity": {
            "mode": anonymity_mode,
            "tally": tally_mode,
            "anti_coercion": anti_coercion,
        },
        "weighting": {
            "mode": weighting_mode,
            "params": weighting_params,
        },
        "timeline": {
            "opens_at": opens_at,
            "closes_at": closes_at,
            "timezone": timezone,
        },
    }

    if proof_policy:
        manifest["proof_policy"] = proof_policy

    if extra:
        manifest["extra"] = extra

    return manifest


def _sign_manifest_inplace(manifest: Dict[str, Any], *, keystore_path: Path) -> None:
    """
    Adds a 'signature' object to the manifest:
      - did
      - public_key_b64
      - signature (over canonical JSON of manifest WITHOUT signature)
      - signed_payload_sha256
    """
    # strip any existing signature for signing
    body = dict(manifest)
    body.pop("signature", None)

    payload = _canonical_dumps(body).encode("utf-8")
    payload_hash = _sha256_hex(payload)

    from coherenceledger.keystore import KeyStore  # type: ignore
    from coherenceledger.crypto import b64encode  # type: ignore

    ks = KeyStore(path=keystore_path)
    did, kp = ks.load_keypair()

    sig = kp.sign(payload)

    manifest["signature"] = {
        "did": did.did,
        "public_key_b64": b64encode(kp.public_bytes_raw()),
        "signature": b64encode(sig),
        "signed_payload_sha256": payload_hash,
        "signed_at": _utc_now_iso(),
        "alg": "Ed25519",
        "canon": "JCS" if "coherenceledger" in str(type(payload)) else "canonical-json",
    }


def _anchor_manifest_file(
    *,
    manifest_path: Path,
    ledger_path: Path,
    keystore_path: Path,
    repo_root: Optional[Path],
    purpose: str,
) -> Dict[str, str]:
    """
    Append a ledger event anchoring the vote manifest artifact.
    Returns {event_id, seal}.
    """
    from coherenceledger.schemas import LedgerEvent  # type: ignore
    from coherenceledger.ledger import Ledger        # type: ignore
    from coherenceledger.keystore import KeyStore    # type: ignore
    from coherenceledger.crypto import b64encode     # type: ignore

    ledger = Ledger(path=ledger_path)
    ks = KeyStore(path=keystore_path)
    did, kp = ks.load_keypair()

    payload: Dict[str, Any] = {
        "artifact_type": "ucc.vote_manifest",
        "vote_manifest_path": _safe_relpath(manifest_path, repo_root),
        "vote_manifest_sha256": _sha256_file(manifest_path),
    }

    # shallow extract of a few purpose-bound fields (non-sensitive)
    try:
        m = json.loads(manifest_path.read_text(encoding="utf-8"))
        payload["manifest_id"] = m.get("manifest_id")
        p = m.get("purpose", {}) if isinstance(m, dict) else {}
        payload["purpose_id"] = p.get("id")
        payload["scope"] = p.get("scope")
        a = m.get("anonymity", {}) if isinstance(m, dict) else {}
        w = m.get("weighting", {}) if isinstance(m, dict) else {}
        e = m.get("electorate", {}) if isinstance(m, dict) else {}
        payload["anonymity_mode"] = a.get("mode")
        payload["tally_mode"] = a.get("tally")
        payload["weighting_mode"] = w.get("mode")
        payload["electorate_type"] = e.get("type")
    except Exception:
        pass

    ev = LedgerEvent.create_unsigned(
        actor_did=did.did,
        purpose=purpose,
        event_type="ucc.vote_manifest.anchor",
        payload=payload,
        prev_seal=ledger.last_seal(),
    )
    sig = kp.sign(ev.signing_payload())
    ev.signature = b64encode(sig)
    ev.public_key_b64 = b64encode(kp.public_bytes_raw())

    ledger.append(ev)
    ledger.verify()
    return {"event_id": ev.event_id, "seal": ev.seal}


def write_vote_manifest(
    *,
    outdir: Path,
    manifest: Dict[str, Any],
    sign: bool = False,
    anchor: bool = False,
    repo_root: Optional[Path] = None,
    keystore_path: Optional[Path] = None,
    ledger_path: Optional[Path] = None,
    ledger_purpose: str = "ucc.vote_manifest.anchor",
) -> Path:
    """
    Writes vote_manifest.json into outdir.
    Optionally signs the manifest and anchors it into CoherenceLedger.
    """
    outdir = outdir.resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    repo_root = repo_root.resolve() if repo_root else None

    # infer repo root when used inside CoherenceLattice/ucc
    if repo_root is None:
        # CoherenceLattice/ucc/src/ucc/vote_manifest.py -> parents[3] == repo root
        repo_root = Path(__file__).resolve().parents[3]

    keystore_path = (keystore_path or (repo_root / ".secrets" / "coherenceledger_keystore.json")).resolve()
    ledger_path = (ledger_path or (repo_root / "ledger.jsonl")).resolve()

    if sign:
        _sign_manifest_inplace(manifest, keystore_path=keystore_path)

    path = outdir / "vote_manifest.json"
    path.write_text(
        json.dumps(manifest, ensure_ascii=False, separators=(",", ":"), sort_keys=True),
        encoding="utf-8",
    )

    if anchor:
        _anchor_manifest_file(
            manifest_path=path,
            ledger_path=ledger_path,
            keystore_path=keystore_path,
            repo_root=repo_root,
            purpose=ledger_purpose,
        )

    return path


def write_vote_manifest_env(
    *,
    outdir: Path,
    manifest: Dict[str, Any],
) -> Path:
    """
    Convenience wrapper:
      - if COHERENCELEDGER_ENABLE truthy -> sign + anchor
      - else -> just write
    """
    enable = _truthy_env("COHERENCELEDGER_ENABLE")
    strict = _truthy_env("COHERENCELEDGER_STRICT")
    purpose = os.getenv("COHERENCELEDGER_PURPOSE", "ucc.vote_manifest.anchor")

    repo_root = Path(__file__).resolve().parents[3]
    keystore = Path(os.getenv("COHERENCELEDGER_KEYSTORE", str(repo_root / ".secrets" / "coherenceledger_keystore.json")))
    ledger = Path(os.getenv("COHERENCELEDGER_LEDGER", str(repo_root / "ledger.jsonl")))

    if enable and not keystore.exists():
        if strict:
            raise FileNotFoundError(f"CoherenceLedger keystore missing: {keystore}")
        enable = False

    if enable:
        try:
            return write_vote_manifest(
                outdir=outdir,
                manifest=manifest,
                sign=True,
                anchor=True,
                repo_root=repo_root,
                keystore_path=keystore,
                ledger_path=ledger,
                ledger_purpose=purpose,
            )
        except Exception:
            if strict:
                raise
            return write_vote_manifest(outdir=outdir, manifest=manifest)
    else:
        return write_vote_manifest(outdir=outdir, manifest=manifest)
