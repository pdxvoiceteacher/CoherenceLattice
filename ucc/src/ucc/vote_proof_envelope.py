from __future__ import annotations

from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional
import base64
import hashlib
import json
import os

from cryptography.hazmat.primitives.ciphers.aead import AESGCM

from ucc.verifier_registry import DEFAULT_VERIFIER_ID, get_spec, load_registry
from ucc.proof_verifiers import proof_stub_b64, verify_envelope
from ucc.circuit_registry import load_and_pin_circuit_descriptor
from ucc.public_inputs import build_public_inputs_spec


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _truthy_env(name: str) -> bool:
    return os.getenv(name, "").strip().lower() in {"1","true","yes","y","on"}


def _sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_hex(path.read_bytes())


def _safe_relpath(path: Path, base: Optional[Path]) -> str:
    try:
        return str(path.resolve().relative_to(base.resolve())) if base else str(path.resolve())
    except Exception:
        return str(path.resolve())


def _aad_bytes(manifest_id: str, ballot_id: str, nullifier_sha256: str) -> bytes:
    s = f"manifest_id={manifest_id}|ballot_id={ballot_id}|nullifier_sha256={nullifier_sha256}"
    return s.encode("utf-8")


def choice_hash(choice: str) -> str:
    return _sha256_hex(choice.encode("utf-8"))


def build_proof_envelope_from_commit_and_reveal(commit: dict, reveal: dict, verifier_id: str = DEFAULT_VERIFIER_ID) -> dict:
    registry = load_registry()
    spec = get_spec(verifier_id, registry)

    # v1.6: circuit pinning (verifier_id -> circuit_id -> circuit_sha256)
    c_id = spec.get('circuit_id')
    c_sha = None
    if c_id:
        cinfo = load_and_pin_circuit_descriptor(str(c_id))
        c_sha = cinfo['sha256']


    manifest_id = str(commit["manifest_id"])
    ballot_id = str(commit["ballot_id"])
    nullifier_sha256 = str(commit["nullifier_sha256"])
    ct_sha = str(commit["ciphertext_sha256"])
    aad_sha = str(commit["aad_sha256"])

    nonce = base64.b64decode(commit["nonce_b64"])
    ct = base64.b64decode(commit["ciphertext_b64"])
    key = base64.b64decode(reveal["key_b64"])

    if _sha256_hex(ct) != ct_sha:
        raise ValueError("ciphertext_sha256 mismatch with commit bytes")

    aad = _aad_bytes(manifest_id, ballot_id, nullifier_sha256)
    if _sha256_hex(aad) != aad_sha:
        raise ValueError("aad_sha256 mismatch with computed AAD")

    aesgcm = AESGCM(key)
    pt = aesgcm.decrypt(nonce, ct, aad).decode("utf-8")
    ch = choice_hash(pt)

    public_signals = {
        "manifest_id": manifest_id,
        "ballot_id": ballot_id,
        "nullifier_sha256": nullifier_sha256,
        "ciphertext_sha256": ct_sha,
        "aad_sha256": aad_sha,
        "choice_hash": ch,
    }

    # v1.4: embed versioned snarkjs public input vector
    public_signals["public_inputs"] = build_public_inputs_spec(public_signals)

    return {
        "version": 2,
        "schema_id": "ucc.vote_proof_envelope.v0_5",
        "created_at": _utc_now_iso(),
        "verifier_id": verifier_id,
        "vk_sha256": spec.get("vk_sha256"),
        "circuit_id": spec.get("circuit_id"),
        "circuit_sha256": c_sha,
        "public_signals": public_signals,
        "proof_b64": proof_stub_b64(public_signals),
        "proof_alg": spec.get("alg", "PROOF_STUB_SHA256"),
    }


def verify_proof_envelope(doc: dict, registry: Optional[Dict[str, Dict[str, Any]]] = None) -> None:
    verify_envelope(doc, registry=registry)


def _anchor_artifact(
    *,
    proof_path: Path,
    manifest_id: str,
    ledger_path: Path,
    keystore_path: Path,
    repo_root: Optional[Path],
    purpose: str,
) -> None:
    from coherenceledger.schemas import LedgerEvent  # type: ignore
    from coherenceledger.ledger import Ledger        # type: ignore
    from coherenceledger.keystore import KeyStore    # type: ignore
    from coherenceledger.crypto import b64encode     # type: ignore

    ledger = Ledger(path=ledger_path)
    ks = KeyStore(path=keystore_path)
    did, kp = ks.load_keypair()

    payload = {
        "artifact_type": "ucc.vote_proof_envelope",
        "manifest_id": manifest_id,
        "proof_path": _safe_relpath(proof_path, repo_root),
        "proof_sha256": _sha256_file(proof_path),
    }

    ev = LedgerEvent.create_unsigned(
        actor_did=did.did,
        purpose=purpose,
        event_type="ucc.vote_proof_envelope.anchor",
        payload=payload,
        prev_seal=ledger.last_seal(),
    )
    sig = kp.sign(ev.signing_payload())
    ev.signature = b64encode(sig)
    ev.public_key_b64 = b64encode(kp.public_bytes_raw())
    ledger.append(ev)
    ledger.verify()


def write_proof_envelope(outdir: Path, proof_doc: dict, repo_root: Optional[Path] = None) -> Path:
    outdir = outdir.resolve()
    proofs_dir = outdir / "secret_v03" / "proofs"
    proofs_dir.mkdir(parents=True, exist_ok=True)

    ps = proof_doc["public_signals"]
    ballot_id = ps["ballot_id"]
    manifest_id = ps["manifest_id"]

    proof_path = proofs_dir / f"proof_{ballot_id}.json"
    proof_path.write_text(json.dumps(proof_doc, ensure_ascii=False, separators=(",", ":"), sort_keys=True), encoding="utf-8")

    if _truthy_env("COHERENCELEDGER_ENABLE"):
        repo_root = repo_root.resolve() if repo_root else Path(__file__).resolve().parents[3]
        keystore = Path(os.getenv("COHERENCELEDGER_KEYSTORE", str(repo_root / ".secrets" / "coherenceledger_keystore.json")))
        ledger = Path(os.getenv("COHERENCELEDGER_LEDGER", str(repo_root / "ledger.jsonl")))
        purpose = os.getenv("COHERENCELEDGER_PROOF_PURPOSE", "ucc.vote_proof_envelope.anchor")
        if _truthy_env("COHERENCELEDGER_STRICT") and not keystore.exists():
            raise FileNotFoundError(f"keystore missing: {keystore}")
        if keystore.exists():
            _anchor_artifact(
                proof_path=proof_path,
                manifest_id=str(manifest_id),
                ledger_path=ledger,
                keystore_path=keystore,
                repo_root=repo_root,
                purpose=purpose,
            )

    return proof_path
