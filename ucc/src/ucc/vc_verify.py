from __future__ import annotations

from pathlib import Path
from typing import Any, Dict, Optional, List
import json
import hashlib

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

from ucc.didkey import did_key_to_ed25519_pubkey_bytes
from ucc.vc_registry import load_registry, is_revoked


def _canonical_json(obj: Any) -> str:
    try:
        from coherenceledger import jcs  # type: ignore
        return jcs.dumps(obj)
    except Exception:
        return json.dumps(obj, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def b64url_decode(s: str) -> bytes:
    # coherenceledger uses urlsafe base64 without padding; handle both
    import base64
    s = s.strip()
    pad = "=" * ((4 - len(s) % 4) % 4)
    return base64.urlsafe_b64decode(s + pad)


def verify_vc_signature(vc: Dict[str, Any]) -> None:
    """
    Verifies our VC proof:
      - payload_sha256 matches canonical VC without proof
      - Ed25519 signature verifies against issuer DID in proof.verificationMethod
    """
    if not isinstance(vc, dict):
        raise ValueError("vc must be object")

    proof = vc.get("proof")
    if not isinstance(proof, dict):
        raise ValueError("vc missing proof")

    vm = proof.get("verificationMethod", "")
    if not isinstance(vm, str) or "#key-1" not in vm:
        raise ValueError("proof.verificationMethod must be 'did:key:...#key-1'")
    issuer_did = vm.split("#", 1)[0]

    body = dict(vc)
    body.pop("proof", None)
    canon = _canonical_json(body).encode("utf-8")
    psha = sha256_hex(canon)

    if proof.get("payload_sha256") != psha:
        raise ValueError("payload_sha256 mismatch")

    sig = b64url_decode(str(proof.get("jws", "")))
    pk_bytes = did_key_to_ed25519_pubkey_bytes(issuer_did)
    pub = Ed25519PublicKey.from_public_bytes(pk_bytes)
    pub.verify(sig, canon)


def vc_sha256(vc: Dict[str, Any]) -> str:
    return sha256_hex(_canonical_json(vc).encode("utf-8"))


def vc_file_for_id(registry_path: Path, vc_id: str) -> Path:
    # issue_vc writes vc_<id with : replaced>.json in registry directory
    name = f"vc_{vc_id.replace(':','_')}.json"
    return registry_path.parent / name


def find_valid_vc_for_subject(
    *,
    registry_path: Path,
    subject_did: str,
    vc_type: str,
    issuer_did: Optional[str] = None,
) -> Dict[str, Any]:
    reg = load_registry(registry_path)
    for e in reg.get("entries", []):
        if e.get("subject_did") != subject_did:
            continue
        types = e.get("types", [])
        if vc_type not in types:
            continue
        if issuer_did and e.get("issuer_did") != issuer_did:
            continue
        vc_id = e.get("vc_id")
        if not vc_id or is_revoked(reg, vc_id):
            continue

        vc_path = vc_file_for_id(registry_path, vc_id)
        if not vc_path.exists():
            continue

        vc = json.loads(vc_path.read_text(encoding="utf-8-sig"))
        # hash matches registry
        if e.get("vc_sha256") and e["vc_sha256"] != vc_sha256(vc):
            continue
        # signature verifies
        verify_vc_signature(vc)
        return vc

    raise ValueError("no valid (unrevoked, verified) VC found for subject")


def assert_subject_has_valid_vc_if_configured(*, subject_did: str, manifest: Dict[str, Any], repo_root: Path) -> None:
    """
    Enforces did_vc electorate IF it is configured with:
      electorate.type == did_vc
      electorate.rules.vc_type present
      electorate.rules.issuer_did (or issuer starting with did:)
    Registry path:
      electorate.rules.registry_path OR env UCC_VC_REGISTRY OR default governance/identity/vc_registry.json
    """
    electorate = manifest.get("electorate")
    if not isinstance(electorate, dict) or electorate.get("type") != "did_vc":
        return

    rules = electorate.get("rules") or {}
    if not isinstance(rules, dict):
        return

    vc_type = rules.get("vc_type") or rules.get("credential_type")
    issuer = rules.get("issuer_did") or rules.get("issuer")
    if not isinstance(vc_type, str) or not vc_type:
        return
    if not isinstance(issuer, str) or not issuer.startswith("did:"):
        # not configured for cryptographic verification yet
        return

    reg_path = rules.get("registry_path") or os.getenv("UCC_VC_REGISTRY", "")
    if isinstance(reg_path, str) and reg_path:
        p = Path(reg_path)
        registry_path = p if p.is_absolute() else (repo_root / p)
    else:
        registry_path = repo_root / "governance" / "identity" / "vc_registry.json"

    find_valid_vc_for_subject(registry_path=registry_path, subject_did=subject_did, vc_type=vc_type, issuer_did=issuer)
