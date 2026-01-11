from __future__ import annotations

"""
Secret Tally v0.1 (commit–reveal + nullifiers)

Reads:
  outdir/secret/commits/commit_*.json
  outdir/secret/reveals/reveal_*.json

Counts ONLY revealed ballots that match their commitments.
Rejects:
  - duplicate nullifiers
  - reveals without matching commit
  - commitment mismatch

Writes:
  outdir/secret/tally.json

Optionally signs + anchors tally (system DID) when COHERENCELEDGER_ENABLE truthy.
"""

from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional
from uuid import uuid4

import hashlib
import json
import os


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


def _commitment_for_choice(choice: str, salt_hex: str) -> str:
    body = _canonical_dumps({"choice": choice}).encode("utf-8")
    return _sha256_hex(body + bytes.fromhex(salt_hex))


def _anchor(
    *,
    tally_path: Path,
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
        "artifact_type": "ucc.vote_tally_secret",
        "manifest_id": manifest_id,
        "tally_path": _safe_relpath(tally_path, repo_root),
        "tally_sha256": _sha256_file(tally_path),
    }

    ev = LedgerEvent.create_unsigned(
        actor_did=did.did,
        purpose=purpose,
        event_type="ucc.vote_tally_secret.anchor",
        payload=payload,
        prev_seal=ledger.last_seal(),
    )
    sig = kp.sign(ev.signing_payload())
    ev.signature = b64encode(sig)
    ev.public_key_b64 = b64encode(kp.public_bytes_raw())
    ledger.append(ev)
    ledger.verify()


def tally_secret(
    *,
    outdir: Path,
    manifest_id: str,
    strict: bool = False,
) -> Dict[str, Any]:
    secret_dir = outdir / "secret"
    commits_dir = secret_dir / "commits"
    reveals_dir = secret_dir / "reveals"

    commits: Dict[str, dict] = {}
    nullifiers_seen: set[str] = set()
    dup_nullifiers: List[str] = []

    seen_commits = 0
    for cp in commits_dir.glob("commit_*.json") if commits_dir.exists() else []:
        seen_commits += 1
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

    reveals: Dict[str, dict] = {}
    seen_reveals = 0
    for rp in reveals_dir.glob("reveal_*.json") if reveals_dir.exists() else []:
        seen_reveals += 1
        r = _load_json(rp)
        bid = r.get("ballot_id")
        if isinstance(bid, str) and bid:
            reveals[bid] = r

    counts: Dict[str, int] = {}
    valid = 0
    invalid = 0
    invalid_reasons: List[Dict[str, str]] = []

    for bid, c in commits.items():
        r = reveals.get(bid)
        if not r:
            invalid += 1
            if strict:
                invalid_reasons.append({"ballot_id": bid, "reason": "missing reveal"})
            continue

        choice = r.get("choice")
        salt = r.get("salt_hex")
        com = c.get("commitment")
        if not isinstance(choice, str) or not isinstance(salt, str) or not isinstance(com, str):
            invalid += 1
            if strict:
                invalid_reasons.append({"ballot_id": bid, "reason": "malformed reveal/commit"})
            continue

        recomputed = _commitment_for_choice(choice, salt)
        if recomputed != com:
            invalid += 1
            if strict:
                invalid_reasons.append({"ballot_id": bid, "reason": "commitment mismatch"})
            continue

        counts[choice] = counts.get(choice, 0) + 1
        valid += 1

    passed = (len(dup_nullifiers) == 0)

    return {
        "version": 1,
        "schema_id": "ucc.vote_tally_secret.v0_1",
        "tally_id": str(uuid4()),
        "created_at": _utc_now_iso(),
        "manifest_id": manifest_id,
        "passed_nullifier_check": passed,
        "commits": {"seen": seen_commits},
        "reveals": {"seen": seen_reveals},
        "ballots": {"valid": valid, "invalid": invalid},
        "counts": counts,
        "dup_nullifiers": dup_nullifiers if strict else [],
        "invalid_reasons": invalid_reasons if strict else [],
    }


def write_tally_secret(outdir: Path, manifest_id: str) -> Path:
    outdir = outdir.resolve()
    secret_dir = outdir / "secret"
    secret_dir.mkdir(parents=True, exist_ok=True)

    strict = _truthy_env("COHERENCELEDGER_STRICT")
    tally = tally_secret(outdir=outdir, manifest_id=manifest_id, strict=strict)

    # optional system DID signature of tally artifact
    enable = _truthy_env("COHERENCELEDGER_ENABLE")
    repo_root = Path(__file__).resolve().parents[3]
    keystore = Path(os.getenv("COHERENCELEDGER_KEYSTORE", str(repo_root / ".secrets" / "coherenceledger_keystore.json")))
    ledger = Path(os.getenv("COHERENCELEDGER_LEDGER", str(repo_root / "ledger.jsonl")))
    purpose = os.getenv("COHERENCELEDGER_PURPOSE", "ucc.vote_tally_secret.anchor")

    if enable and keystore.exists():
        # sign tally JSON
        from coherenceledger.keystore import KeyStore  # type: ignore
        from coherenceledger.crypto import b64encode  # type: ignore
        body = dict(tally)
        body.pop("signature", None)
        payload = _canonical_dumps(body).encode("utf-8")
        payload_hash = _sha256_hex(payload)

        ks = KeyStore(path=keystore)
        did, kp = ks.load_keypair()
        sig = kp.sign(payload)
        tally["signature"] = {
            "did": did.did,
            "public_key_b64": b64encode(kp.public_bytes_raw()),
            "signature": b64encode(sig),
            "signed_payload_sha256": payload_hash,
            "signed_at": _utc_now_iso(),
            "alg": "Ed25519",
            "canon": "canonical-json",
        }

    tally_path = secret_dir / "tally.json"
    tally_path.write_text(
        json.dumps(tally, ensure_ascii=False, separators=(",", ":"), sort_keys=True),
        encoding="utf-8",
    )

    if enable:
        if _truthy_env("COHERENCELEDGER_STRICT") and not keystore.exists():
            raise FileNotFoundError(f"keystore missing: {keystore}")
        if keystore.exists():
            _anchor(
                tally_path=tally_path,
                manifest_id=manifest_id,
                ledger_path=ledger,
                keystore_path=keystore,
                repo_root=repo_root,
                purpose=purpose,
            )

    return tally_path
