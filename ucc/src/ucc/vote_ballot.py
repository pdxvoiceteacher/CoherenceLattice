"""
Ballots v0 (purpose-bound to Vote Manifest v0)

A ballot is an individual vote that references a manifest_id.
This v0 supports OPEN ballots with DID signatures + ledger anchoring.

Rules:
- Ballot must reference a manifest.
- If manifest.anonymity.mode != "open", then DID signing is disallowed in STRICT mode.
  (Later ZK/anonymous ballots will be separate.)
- Optional ledger anchoring when COHERENCELEDGER_ENABLE is truthy.

Cross-platform: pathlib, no shell deps.
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


BALLOT_SCHEMA_ID = "ucc.vote_ballot.v0"


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _truthy_env(name: str) -> bool:
    return os.getenv(name, "").strip().lower() in {"1", "true", "yes", "y", "on"}


def _canonical_dumps(obj: Any) -> str:
    """
    Deterministic JSON serialization.
    If coherenceledger.jcs exists, use it; else stable json.dumps.
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


def load_manifest(path: Path) -> Dict[str, Any]:
    # tolerate BOM just in case
    txt = path.read_text(encoding="utf-8-sig")
    return json.loads(txt)


def build_ballot(
    *,
    manifest_id: str,
    ballot_type: str,
    selection: Any,
    title: Optional[str] = None,
    extra: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    ballot: Dict[str, Any] = {
        "version": 1,
        "schema_id": BALLOT_SCHEMA_ID,
        "ballot_id": str(uuid4()),
        "created_at": _utc_now_iso(),
        "manifest_id": manifest_id,
        "ballot": {
            "type": ballot_type,     # e.g. "single_choice" | "approval" | "ranked"
            "selection": selection,  # schema depends on type
        },
    }
    if title:
        ballot["title"] = title
    if extra:
        ballot["extra"] = extra
    return ballot


def _sign_ballot_inplace(ballot: Dict[str, Any], *, keystore_path: Path) -> None:
    """
    Adds 'signature' object:
      - did
      - public_key_b64
      - signature (over canonical JSON of ballot WITHOUT signature)
      - signed_payload_sha256
    """
    body = dict(ballot)
    body.pop("signature", None)

    payload = _canonical_dumps(body).encode("utf-8")
    payload_hash = _sha256_hex(payload)

    from coherenceledger.keystore import KeyStore  # type: ignore
    from coherenceledger.crypto import b64encode  # type: ignore

    ks = KeyStore(path=keystore_path)
    did, kp = ks.load_keypair()

    sig = kp.sign(payload)

    ballot["signature"] = {
        "did": did.did,
        "public_key_b64": b64encode(kp.public_bytes_raw()),
        "signature": b64encode(sig),
        "signed_payload_sha256": payload_hash,
        "signed_at": _utc_now_iso(),
        "alg": "Ed25519",
        "canon": "canonical-json",
    }


def _anchor_ballot_file(
    *,
    ballot_path: Path,
    manifest_id: str,
    ledger_path: Path,
    keystore_path: Path,
    repo_root: Optional[Path],
    purpose: str,
) -> Dict[str, str]:
    """
    Append ledger event anchoring the ballot artifact.
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
        "artifact_type": "ucc.vote_ballot",
        "manifest_id": manifest_id,
        "vote_ballot_path": _safe_relpath(ballot_path, repo_root),
        "vote_ballot_sha256": _sha256_file(ballot_path),
    }

    # Include a few non-sensitive fields for audit/search
    try:
        b = json.loads(ballot_path.read_text(encoding="utf-8-sig"))
        payload["ballot_id"] = b.get("ballot_id")
        bt = b.get("ballot", {}) if isinstance(b, dict) else {}
        payload["ballot_type"] = bt.get("type")
    except Exception:
        pass

    ev = LedgerEvent.create_unsigned(
        actor_did=did.did,
        purpose=purpose,
        event_type="ucc.vote_ballot.anchor",
        payload=payload,
        prev_seal=ledger.last_seal(),
    )
    sig = kp.sign(ev.signing_payload())
    ev.signature = b64encode(sig)
    ev.public_key_b64 = b64encode(kp.public_bytes_raw())

    ledger.append(ev)
    ledger.verify()
    return {"event_id": ev.event_id, "seal": ev.seal}


def write_ballot(
    *,
    outdir: Path,
    ballot: Dict[str, Any],
    manifest: Dict[str, Any],
    sign: bool = False,
    anchor: bool = False,
    repo_root: Optional[Path] = None,
    keystore_path: Optional[Path] = None,
    ledger_path: Optional[Path] = None,
    ledger_purpose: str = "ucc.vote_ballot.cast",
) -> Path:
    """
    Writes a ballot JSON file into outdir/ballots/.
    Optionally signs and anchors into CoherenceLedger.

    Enforces: if manifest.anonymity.mode != open and sign requested in strict mode -> error.
    """
    outdir = outdir.resolve()
    (outdir / "ballots").mkdir(parents=True, exist_ok=True)

    repo_root = repo_root.resolve() if repo_root else None
    if repo_root is None:
        repo_root = Path(__file__).resolve().parents[3]

    keystore_path = (keystore_path or (repo_root / ".secrets" / "coherenceledger_keystore.json")).resolve()
    ledger_path = (ledger_path or (repo_root / "ledger.jsonl")).resolve()

    anon_mode = (manifest.get("anonymity", {}) or {}).get("mode", "open")
    strict = _truthy_env("COHERENCELEDGER_STRICT")

    if sign and anon_mode != "open" and strict:
        raise ValueError(f"Manifest anonymity mode '{anon_mode}' forbids DID signing in strict mode.")


    # VOTE_REGISTRY_ENFORCE: open-mode replay protection (one ballot per DID in strict unless overridden)
    if sign and anon_mode == "open":
        # determine max ballots per DID
        rules = (manifest.get("electorate") or {}).get("rules") or {}
        max_raw = rules.get("max_ballots_per_did", None)

        if max_raw is None:
            max_per_did = 1 if strict else 0
        else:
            try:
                max_per_did = int(max_raw)
            except Exception:
                max_per_did = 1 if strict else 0

        if max_per_did > 0:
            from coherenceledger.keystore import KeyStore  # type: ignore
            from ucc.vote_registry import enforce_max_ballots_per_did

            ks = KeyStore(path=keystore_path)
            did_obj, _kp = ks.load_keypair()
            enforce_max_ballots_per_did(outdir / "ballots", did_obj.did, max_per_did)

            # VOTE_VC_ENFORCE: did_vc electorate membership (if configured with issuer DID + vc_type)
            try:
                from ucc.vc_verify import assert_subject_has_valid_vc_if_configured
                assert_subject_has_valid_vc_if_configured(subject_did=did_obj.did, manifest=manifest, repo_root=repo_root)
            except ImportError:
                pass



    # VOTE_VC_ENFORCE_ALWAYS: did_vc electorate membership (config-gated; runs even if replay limit disabled)
    if sign and anon_mode == "open":
        try:
            from coherenceledger.keystore import KeyStore  # type: ignore
            from ucc.vc_verify import assert_subject_has_valid_vc_if_configured

            ks = KeyStore(path=keystore_path)
            did_obj, _kp = ks.load_keypair()
            assert_subject_has_valid_vc_if_configured(subject_did=did_obj.did, manifest=manifest, repo_root=repo_root)
        except ImportError:
            pass

    if sign:
        _sign_ballot_inplace(ballot, keystore_path=keystore_path)

    ballot_path = (outdir / "ballots" / f"ballot_{ballot['ballot_id']}.json")
    ballot_path.write_text(
        json.dumps(ballot, ensure_ascii=False, separators=(",", ":"), sort_keys=True),
        encoding="utf-8",
    )

    if anchor:
        _anchor_ballot_file(
            ballot_path=ballot_path,
            manifest_id=str(ballot.get("manifest_id")),
            ledger_path=ledger_path,
            keystore_path=keystore_path,
            repo_root=repo_root,
            purpose=ledger_purpose,
        )

    return ballot_path


def write_ballot_env(
    *,
    outdir: Path,
    ballot: Dict[str, Any],
    manifest: Dict[str, Any],
) -> Path:
    """
    Env-gated convenience:
      if COHERENCELEDGER_ENABLE truthy -> sign + anchor
      else -> write only
    """
    enable = _truthy_env("COHERENCELEDGER_ENABLE")
    strict = _truthy_env("COHERENCELEDGER_STRICT")
    purpose = os.getenv("COHERENCELEDGER_PURPOSE", "ucc.vote_ballot.cast")

    repo_root = Path(__file__).resolve().parents[3]
    keystore = Path(os.getenv("COHERENCELEDGER_KEYSTORE", str(repo_root / ".secrets" / "coherenceledger_keystore.json")))
    ledger = Path(os.getenv("COHERENCELEDGER_LEDGER", str(repo_root / "ledger.jsonl")))

    if enable and not keystore.exists():
        if strict:
            raise FileNotFoundError(f"CoherenceLedger keystore missing: {keystore}")
        enable = False

    if enable:
        try:
            return write_ballot(
                outdir=outdir,
                ballot=ballot,
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
            return write_ballot(outdir=outdir, ballot=ballot, manifest=manifest)
    else:
        return write_ballot(outdir=outdir, ballot=ballot, manifest=manifest)
