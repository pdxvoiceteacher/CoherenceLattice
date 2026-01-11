from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional
from uuid import uuid4
import hashlib
import json

from coherenceledger.keystore import KeyStore
from coherenceledger.crypto import b64encode


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _canonical_json(obj: Any) -> str:
    try:
        from coherenceledger import jcs  # type: ignore
        return jcs.dumps(obj)
    except Exception:
        return json.dumps(obj, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def sign_vc(payload: Dict[str, Any], keystore_path: Path) -> Dict[str, Any]:
    """
    Signs a VC payload (without proof) using Ed25519 from coherenceledger keystore.
    Stores proof.jws as URL-safe b64 of signature bytes.
    """
    body = dict(payload)
    body.pop("proof", None)

    canon = _canonical_json(body).encode("utf-8")
    psha = sha256_hex(canon)

    ks = KeyStore(path=keystore_path)
    did, kp = ks.load_keypair()
    sig = kp.sign(canon)

    proof = {
        "type": "Ed25519Signature2020",
        "created": _utc_now_iso(),
        "verificationMethod": f"{did.did}#key-1",
        "proofPurpose": "assertionMethod",
        "jws": b64encode(sig),
        "payload_sha256": psha,
    }
    out = dict(body)
    out["proof"] = proof
    return out


def issue_vc(
    *,
    issuer_did: str,
    subject_did: str,
    types: List[str],
    subject_claims: Dict[str, Any],
    keystore_path: Path,
    expirationDate: Optional[str] = None,
) -> Dict[str, Any]:
    vc_id = f"urn:uuid:{uuid4()}"
    payload: Dict[str, Any] = {
        "schema_id": "ucc.identity.vc.v0_1",
        "version": 1,
        "id": vc_id,
        "type": ["VerifiableCredential"] + list(types),
        "issuer": issuer_did,
        "issuanceDate": _utc_now_iso(),
        "credentialSubject": {"id": subject_did, **subject_claims},
    }
    if expirationDate:
        payload["expirationDate"] = expirationDate

    return sign_vc(payload, keystore_path=keystore_path)


def vc_sha256(vc: Dict[str, Any]) -> str:
    # hash canonical JSON of entire VC
    return sha256_hex(_canonical_json(vc).encode("utf-8"))
