from __future__ import annotations

"""
Secret Ballot v0.2 (ciphertext payload + nullifier, NO DID signature)

⚠ Demo crypto: XOR stream with random key.
This is *not* secure encryption. It is only to provide an "opaque payload" scaffold
so we can later swap in AEAD + ZK without changing the outer workflow.

Writes:
  outdir/secret_v02/commits/commit_<ballot_id>.json   (contains ciphertext_b64 + ciphertext_sha256 + nullifier)
  outdir/secret_v02/reveals/reveal_<ballot_id>.json   (contains key_b64 + plaintext_choice for demo reveal)

Replay protection:
  - nullifier must be unique within commits/

Ledger anchoring:
  - when COHERENCELEDGER_ENABLE truthy, anchor commit/reveal artifacts (system DID)
"""

from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional, Tuple
from uuid import uuid4

import base64
import hashlib
import json
import os
import secrets


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


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _enforce_unique_nullifier(commits_dir: Path, nullifier_hex: str) -> None:
    if not commits_dir.exists():
        return
    for p in commits_dir.glob("commit_*.json"):
        try:
            c = _load_json(p)
            if c.get("nullifier") == nullifier_hex:
                raise ValueError(f"nullifier already used in {p.name}")
        except json.JSONDecodeError:
            continue


def _xor_bytes(data: bytes, key: bytes) -> bytes:
    # repeat key to length
    out = bytearray(len(data))
    for i, b in enumerate(data):
        out[i] = b ^ key[i % len(key)]
    return bytes(out)


def encrypt_choice_demo(choice: str, key: bytes) -> bytes:
    # minimal encoding; deterministic for same choice/key
    pt = choice.encode("utf-8")
    return _xor_bytes(pt, key)


def decrypt_choice_demo(ciphertext: bytes, key: bytes) -> str:
    pt = _xor_bytes(ciphertext, key)
    return pt.decode("utf-8")


def build_cipher_commit_and_reveal(
    *,
    manifest_id: str,
    plaintext_choice: str,
    nullifier_hex: Optional[str] = None,
    key_b64: Optional[str] = None,
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    nullifier_hex = nullifier_hex or secrets.token_hex(16)
    key = base64.b64decode(key_b64) if key_b64 else secrets.token_bytes(16)

    ballot_id = str(uuid4())
    ct = encrypt_choice_demo(plaintext_choice, key)

    commit = {
        "version": 1,
        "schema_id": "ucc.vote_ballot.secret_cipher_commit.v0_2",
        "ballot_id": ballot_id,
        "created_at": _utc_now_iso(),
        "manifest_id": manifest_id,
        "nullifier": nullifier_hex,
        "nullifier_sha256": _sha256_hex(bytes.fromhex(nullifier_hex)),
        "ciphertext_b64": base64.b64encode(ct).decode("ascii"),
        "ciphertext_sha256": _sha256_hex(ct),
        "enc": "DEMO_XOR_STREAM",
    }

    reveal = {
        "version": 1,
        "schema_id": "ucc.vote_ballot.secret_cipher_reveal.v0_2",
        "ballot_id": ballot_id,
        "created_at": _utc_now_iso(),
        "manifest_id": manifest_id,
        # demo reveal payload (not for production)
        "plaintext_choice": plaintext_choice,
        "key_b64": base64.b64encode(key).decode("ascii"),
        "ciphertext_sha256": _sha256_hex(ct),
    }
    return commit, reveal


def _anchor_artifact(
    *,
    event_type: str,
    artifact_type: str,
    artifact_path: Path,
    manifest_id: str,
    nullifier_sha256: Optional[str],
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

    payload: Dict[str, Any] = {
        "artifact_type": artifact_type,
        "manifest_id": manifest_id,
        "path": _safe_relpath(artifact_path, repo_root),
        "sha256": _sha256_file(artifact_path),
    }
    if nullifier_sha256:
        payload["nullifier_sha256"] = nullifier_sha256

    ev = LedgerEvent.create_unsigned(
        actor_did=did.did,
        purpose=purpose,
        event_type=event_type,
        payload=payload,
        prev_seal=ledger.last_seal(),
    )
    sig = kp.sign(ev.signing_payload())
    ev.signature = b64encode(sig)
    ev.public_key_b64 = b64encode(kp.public_bytes_raw())
    ledger.append(ev)
    ledger.verify()


def write_cipher_commit(*, outdir: Path, commit_doc: Dict[str, Any], repo_root: Optional[Path] = None) -> Path:
    outdir = outdir.resolve()
    commits_dir = outdir / "secret_v02" / "commits"
    commits_dir.mkdir(parents=True, exist_ok=True)

    repo_root = repo_root.resolve() if repo_root else Path(__file__).resolve().parents[3]
    _enforce_unique_nullifier(commits_dir, str(commit_doc["nullifier"]))

    cp = commits_dir / f"commit_{commit_doc['ballot_id']}.json"
    cp.write_text(json.dumps(commit_doc, ensure_ascii=False, separators=(",", ":"), sort_keys=True), encoding="utf-8")

    if _truthy_env("COHERENCELEDGER_ENABLE"):
        keystore = Path(os.getenv("COHERENCELEDGER_KEYSTORE", str(repo_root / ".secrets" / "coherenceledger_keystore.json")))
        ledger = Path(os.getenv("COHERENCELEDGER_LEDGER", str(repo_root / "ledger.jsonl")))
        purpose = os.getenv("COHERENCELEDGER_PURPOSE", "ucc.vote_ballot_cipher.commit.anchor")
        if _truthy_env("COHERENCELEDGER_STRICT") and not keystore.exists():
            raise FileNotFoundError(f"keystore missing: {keystore}")
        if keystore.exists():
            _anchor_artifact(
                event_type="ucc.vote_ballot_cipher.commit.anchor",
                artifact_type="ucc.vote_ballot_cipher.commit",
                artifact_path=cp,
                manifest_id=str(commit_doc["manifest_id"]),
                nullifier_sha256=str(commit_doc.get("nullifier_sha256")),
                ledger_path=ledger,
                keystore_path=keystore,
                repo_root=repo_root,
                purpose=purpose,
            )
    return cp


def write_cipher_reveal(*, outdir: Path, reveal_doc: Dict[str, Any], repo_root: Optional[Path] = None) -> Path:
    outdir = outdir.resolve()
    reveals_dir = outdir / "secret_v02" / "reveals"
    reveals_dir.mkdir(parents=True, exist_ok=True)

    repo_root = repo_root.resolve() if repo_root else Path(__file__).resolve().parents[3]
    rp = reveals_dir / f"reveal_{reveal_doc['ballot_id']}.json"
    rp.write_text(json.dumps(reveal_doc, ensure_ascii=False, separators=(",", ":"), sort_keys=True), encoding="utf-8")

    if _truthy_env("COHERENCELEDGER_ENABLE"):
        keystore = Path(os.getenv("COHERENCELEDGER_KEYSTORE", str(repo_root / ".secrets" / "coherenceledger_keystore.json")))
        ledger = Path(os.getenv("COHERENCELEDGER_LEDGER", str(repo_root / "ledger.jsonl")))
        purpose = os.getenv("COHERENCELEDGER_REVEAL_PURPOSE", "ucc.vote_ballot_cipher.reveal.anchor")
        if _truthy_env("COHERENCELEDGER_STRICT") and not keystore.exists():
            raise FileNotFoundError(f"keystore missing: {keystore}")
        if keystore.exists():
            _anchor_artifact(
                event_type="ucc.vote_ballot_cipher.reveal.anchor",
                artifact_type="ucc.vote_ballot_cipher.reveal",
                artifact_path=rp,
                manifest_id=str(reveal_doc["manifest_id"]),
                nullifier_sha256=None,
                ledger_path=ledger,
                keystore_path=keystore,
                repo_root=repo_root,
                purpose=purpose,
            )
    return rp
