from __future__ import annotations

"""
Proof Tally v0.5

Reads:
  secret_v03/commits/commit_*.json   (AEAD commits)
  secret_v03/proofs/proof_*.json     (proof envelopes)

Validates:
  - nullifier uniqueness via commits
  - proof envelope schema + proof_b64
  - public_signals match commit (manifest_id, ballot_id, nullifier_sha256, ciphertext_sha256, aad_sha256)

Counts:
  - counts_by_choice_hash

Optional:
  - if options.json exists (list of strings), map hashes to labels as counts_by_choice.

Writes:
  secret_v03/tally_proof.json

Optionally signs+anchors tally_proof via system DID.
"""

from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional
from uuid import uuid4

import hashlib
import json
import os

from ucc.vote_proof_envelope import verify_proof_envelope, choice_hash


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _truthy_env(name: str) -> bool:
    return os.getenv(name, "").strip().lower() in {"1","true","yes","y","on"}


def _canonical_dumps(obj: Any) -> str:
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


def _load_json(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))


def tally_proofs(outdir: Path, manifest_id: str, strict: bool = False, options_path: Optional[Path] = None) -> dict:
    base = outdir / "secret_v03"
    commits_dir = base / "commits"
    proofs_dir = base / "proofs"

    commits: Dict[str, dict] = {}
    nullifiers_seen: set[str] = set()
    dup_nullifiers: list[str] = []

    for cp in commits_dir.glob("commit_*.json") if commits_dir.exists() else []:
        c = _load_json(cp)
        bid = c.get("ballot_id")
        nul = c.get("nullifier")
        if not isinstance(bid, str) or not bid:
            continue
        if isinstance(nul, str) and nul:
            if nul in nullifiers_seen:
                dup_nullifiers.append(nul)
            nullifiers_seen.add(nul)
        commits[bid] = c

    counts_hash: Dict[str, int] = {}
    valid = 0
    invalid = 0
    invalid_reasons: list[dict[str,str]] = []

    for pp in proofs_dir.glob("proof_*.json") if proofs_dir.exists() else []:
        try:
            doc = _load_json(pp)
            verify_proof_envelope(doc)
            ps = doc["public_signals"]

            if ps.get("manifest_id") != manifest_id:
                raise ValueError("manifest_id mismatch")

            bid = ps.get("ballot_id")
            if bid not in commits:
                raise ValueError("no matching commit for ballot_id")

            c = commits[bid]
            # match critical fields between proof and commit
            if ps.get("nullifier_sha256") != c.get("nullifier_sha256"):
                raise ValueError("nullifier_sha256 mismatch")
            if ps.get("ciphertext_sha256") != c.get("ciphertext_sha256"):
                raise ValueError("ciphertext_sha256 mismatch")
            if ps.get("aad_sha256") != c.get("aad_sha256"):
                raise ValueError("aad_sha256 mismatch")

            ch = ps.get("choice_hash")
            if not isinstance(ch, str) or not ch:
                raise ValueError("choice_hash missing")

            counts_hash[ch] = counts_hash.get(ch, 0) + 1
            valid += 1

        except Exception as e:
            invalid += 1
            if strict:
                invalid_reasons.append({"path": str(pp), "reason": str(e)})

    counts_choice: Dict[str, int] = {}
    if options_path and options_path.exists():
        opts = _load_json(options_path)
        if isinstance(opts, list):
            mapping = {choice_hash(str(o)): str(o) for o in opts}
            for h, n in counts_hash.items():
                label = mapping.get(h, h)
                counts_choice[label] = counts_choice.get(label, 0) + n

    return {
        "version": 1,
        "schema_id": "ucc.vote_tally_proof.v0_5",
        "tally_id": str(uuid4()),
        "created_at": _utc_now_iso(),
        "manifest_id": manifest_id,
        "passed_nullifier_check": (len(dup_nullifiers) == 0),
        "ballots": {"valid": valid, "invalid": invalid},
        "counts_by_choice_hash": counts_hash,
        "counts_by_choice": counts_choice,
        "dup_nullifiers": dup_nullifiers if strict else [],
        "invalid_reasons": invalid_reasons if strict else [],
        "proof_alg": "PROOF_STUB_SHA256",
    }


def write_tally_proofs(outdir: Path, manifest_id: str, options_path: Optional[Path] = None) -> Path:
    outdir = outdir.resolve()
    base = outdir / "secret_v03"
    base.mkdir(parents=True, exist_ok=True)

    strict = _truthy_env("COHERENCELEDGER_STRICT")
    t = tally_proofs(outdir=outdir, manifest_id=manifest_id, strict=strict, options_path=options_path)

    enable = _truthy_env("COHERENCELEDGER_ENABLE")
    repo_root = Path(__file__).resolve().parents[3]
    keystore = Path(os.getenv("COHERENCELEDGER_KEYSTORE", str(repo_root / ".secrets" / "coherenceledger_keystore.json")))
    ledger = Path(os.getenv("COHERENCELEDGER_LEDGER", str(repo_root / "ledger.jsonl")))
    purpose = os.getenv("COHERENCELEDGER_PURPOSE", "ucc.vote_tally_proof.anchor")

    if enable and keystore.exists():
        from coherenceledger.keystore import KeyStore  # type: ignore
        from coherenceledger.crypto import b64encode  # type: ignore
        body = dict(t)
        body.pop("signature", None)
        payload = _canonical_dumps(body).encode("utf-8")
        payload_hash = _sha256_hex(payload)

        ks = KeyStore(path=keystore)
        did, kp = ks.load_keypair()
        sig = kp.sign(payload)
        t["signature"] = {
            "did": did.did,
            "public_key_b64": b64encode(kp.public_bytes_raw()),
            "signature": b64encode(sig),
            "signed_payload_sha256": payload_hash,
            "signed_at": _utc_now_iso(),
            "alg": "Ed25519",
            "canon": "canonical-json",
        }

    tp = base / "tally_proof.json"
    tp.write_text(json.dumps(t, ensure_ascii=False, separators=(",", ":"), sort_keys=True), encoding="utf-8")

    if enable:
        if _truthy_env("COHERENCELEDGER_STRICT") and not keystore.exists():
            raise FileNotFoundError(f"keystore missing: {keystore}")
        if keystore.exists():
            from coherenceledger.schemas import LedgerEvent  # type: ignore
            from coherenceledger.ledger import Ledger        # type: ignore
            from coherenceledger.keystore import KeyStore    # type: ignore
            from coherenceledger.crypto import b64encode     # type: ignore

            led = Ledger(path=ledger)
            ks = KeyStore(path=keystore)
            did, kp = ks.load_keypair()

            payload2 = {
                "artifact_type": "ucc.vote_tally_proof",
                "manifest_id": manifest_id,
                "tally_path": _safe_relpath(tp, repo_root),
                "tally_sha256": _sha256_file(tp),
            }

            ev = LedgerEvent.create_unsigned(
                actor_did=did.did,
                purpose=purpose,
                event_type="ucc.vote_tally_proof.anchor",
                payload=payload2,
                prev_seal=led.last_seal(),
            )
            sig2 = kp.sign(ev.signing_payload())
            ev.signature = b64encode(sig2)
            ev.public_key_b64 = b64encode(kp.public_bytes_raw())
            led.append(ev)
            led.verify()

    return tp
