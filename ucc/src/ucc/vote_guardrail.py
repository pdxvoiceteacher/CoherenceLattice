"""
Vote Purpose Guardrail v0

Audits a Vote Manifest against a policy table keyed by purpose.scope.
Produces:
  - guardrail/report.json
  - guardrail/audit_bundle.json
Optionally:
  - DID-signs report.json
  - ledger-anchors audit_bundle + report when COHERENCELEDGER_ENABLE is truthy

This is the "purpose-bound audit" gate the project requires.
"""
from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional
from uuid import uuid4

import hashlib
import json
import os


GUARDRAIL_SCHEMA_ID = "ucc.vote_guardrail.v0"


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _truthy_env(name: str) -> bool:
    return os.getenv(name, "").strip().lower() in {"1", "true", "yes", "y", "on"}


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


def load_manifest(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _parse_iso(s: str) -> Optional[datetime]:
    if not isinstance(s, str) or not s:
        return None
    s2 = s.replace("Z", "+00:00") if s.endswith("Z") else s
    try:
        return datetime.fromisoformat(s2)
    except Exception:
        return None


# -------------------------
# Purpose policies (v0)
# -------------------------
POLICIES: Dict[str, Dict[str, Any]] = {
    "org.governance": {
        "electorate_types": {"did_vc", "manual_list"},
        "anonymity_modes": {"open", "pseudonymous", "secret"},
        "tally_modes": {"plaintext", "encrypted", "zk"},
        "weighting_modes": {"one_person_one_vote", "coherence", "quadratic"},
        "secret_requires": {
            "tally": {"encrypted", "zk"},
            "anti_coercion": False,  # recommend but not mandatory at v0
        },
    },
    "dao.governance": {
        "electorate_types": {"token_holders", "did_vc", "manual_list"},
        "anonymity_modes": {"open", "pseudonymous", "secret"},
        "tally_modes": {"plaintext", "encrypted", "zk"},
        "weighting_modes": {"token", "quadratic", "coherence", "one_person_one_vote"},
        "secret_requires": {"tally": {"encrypted", "zk"}, "anti_coercion": False},
    },
    "public.deliberation": {
        "electorate_types": {"did_vc", "manual_list"},
        "anonymity_modes": {"pseudonymous", "secret"},  # no open by default
        "tally_modes": {"encrypted", "zk"},             # require protected tally
        "weighting_modes": {"one_person_one_vote", "quadratic", "coherence"},
        "secret_requires": {"tally": {"encrypted", "zk"}, "anti_coercion": True},  # strict here
        "coherence_requires_cap": True,  # if coherence weighting, require params.cap in strict
    },
}


def _v(code: str, path: str, msg: str) -> Dict[str, str]:
    return {"code": code, "path": path, "message": msg}


def audit_vote_manifest(manifest: Dict[str, Any], *, manifest_sha256: str, strict: bool = False) -> Dict[str, Any]:
    violations: List[Dict[str, str]] = []
    warnings: List[Dict[str, str]] = []

    # Basic required fields
    if manifest.get("schema_id") != "ucc.vote_manifest.v0":
        violations.append(_v("schema_id", "schema_id", "manifest schema_id must be ucc.vote_manifest.v0"))

    # Schema hash check (guards against accidental schema drift)
    try:
        from ucc.vote_manifest import schema_sha256 as manifest_schema_sha256
        expected = manifest_schema_sha256()
        got = manifest.get("schema_sha256")
        if got != expected:
            violations.append(_v("schema_sha256", "schema_sha256", f"schema_sha256 mismatch (got {got}, expected {expected})"))
    except Exception:
        warnings.append(_v("schema_sha256_skip", "schema_sha256", "could not compute schema_sha256; skipping check"))

    purpose = manifest.get("purpose", {}) if isinstance(manifest.get("purpose"), dict) else {}
    scope = purpose.get("scope")
    audit_required = purpose.get("audit_required", True)
    if audit_required is not True:
        violations.append(_v("audit_required", "purpose.audit_required", "purpose.audit_required must be true"))

    if not scope or scope not in POLICIES:
        violations.append(_v("scope", "purpose.scope", f"unsupported scope '{scope}'. Expected one of: {sorted(POLICIES.keys())}"))
        policy = None
    else:
        policy = POLICIES[scope]

    electorate = manifest.get("electorate", {}) if isinstance(manifest.get("electorate"), dict) else {}
    anonymity = manifest.get("anonymity", {}) if isinstance(manifest.get("anonymity"), dict) else {}
    weighting = manifest.get("weighting", {}) if isinstance(manifest.get("weighting"), dict) else {}
    timeline = manifest.get("timeline", {}) if isinstance(manifest.get("timeline"), dict) else {}

    e_type = electorate.get("type")
    a_mode = anonymity.get("mode")
    t_mode = anonymity.get("tally")
    anti = bool(anonymity.get("anti_coercion", False))
    w_mode = weighting.get("mode")
    w_params = weighting.get("params", {}) if isinstance(weighting.get("params"), dict) else {}

    # Timeline sanity
    opens = _parse_iso(str(timeline.get("opens_at", "")))
    closes = _parse_iso(str(timeline.get("closes_at", "")))
    if opens and closes and opens > closes:
        violations.append(_v("timeline", "timeline", "opens_at must be <= closes_at"))
    if not opens or not closes:
        warnings.append(_v("timeline_parse", "timeline", "could not parse opens_at/closes_at as ISO timestamps"))

    # Apply policy constraints
    if policy:
        if e_type not in policy["electorate_types"]:
            violations.append(_v("electorate.type", "electorate.type", f"electorate.type '{e_type}' not allowed for scope '{scope}'"))

        if a_mode not in policy["anonymity_modes"]:
            violations.append(_v("anonymity.mode", "anonymity.mode", f"anonymity.mode '{a_mode}' not allowed for scope '{scope}'"))

        if t_mode not in policy["tally_modes"]:
            violations.append(_v("anonymity.tally", "anonymity.tally", f"tally mode '{t_mode}' not allowed for scope '{scope}'"))

        if w_mode not in policy["weighting_modes"]:
            violations.append(_v("weighting.mode", "weighting.mode", f"weighting.mode '{w_mode}' not allowed for scope '{scope}'"))

        # Secret constraints
        if a_mode == "secret":
            req = policy.get("secret_requires", {})
            if "tally" in req and t_mode not in set(req["tally"]):
                violations.append(_v("secret.tally", "anonymity.tally", f"secret ballots require tally in {sorted(req['tally'])}"))
            if req.get("anti_coercion", False) and anti is not True:
                violations.append(_v("secret.anti_coercion", "anonymity.anti_coercion", "secret ballots require anti_coercion=true"))

        # Public deliberation coherence weighting requires cap in strict mode
        if policy.get("coherence_requires_cap") and w_mode == "coherence" and strict:
            if "cap" not in w_params:
                violations.append(_v("coherence.cap", "weighting.params.cap", "coherence weighting requires params.cap in strict mode"))

    passed = len(violations) == 0

    report: Dict[str, Any] = {
        "version": 1,
        "schema_id": GUARDRAIL_SCHEMA_ID,
        "report_id": str(uuid4()),
        "created_at": _utc_now_iso(),
        "manifest_id": manifest.get("manifest_id"),
        "manifest_sha256": manifest_sha256,
        "scope": scope,
        "passed": passed,
        "violations": violations,
        "warnings": warnings,
        "policy_version": 1,
        "strict": bool(strict),
    }
    return report


def _sign_inplace(doc: Dict[str, Any], *, keystore_path: Path) -> None:
    body = dict(doc)
    body.pop("signature", None)

    payload = _canonical_dumps(body).encode("utf-8")
    payload_hash = _sha256_hex(payload)

    from coherenceledger.keystore import KeyStore  # type: ignore
    from coherenceledger.crypto import b64encode  # type: ignore

    ks = KeyStore(path=keystore_path)
    did, kp = ks.load_keypair()
    sig = kp.sign(payload)

    doc["signature"] = {
        "did": did.did,
        "public_key_b64": b64encode(kp.public_bytes_raw()),
        "signature": b64encode(sig),
        "signed_payload_sha256": payload_hash,
        "signed_at": _utc_now_iso(),
        "alg": "Ed25519",
        "canon": "canonical-json",
    }


def _anchor_guardrail_bundle(
    *,
    audit_bundle_path: Path,
    report_path: Path,
    manifest_id: str,
    manifest_sha256: str,
    ledger_path: Path,
    keystore_path: Path,
    repo_root: Optional[Path],
    purpose: str,
) -> Dict[str, str]:
    from coherenceledger.schemas import LedgerEvent  # type: ignore
    from coherenceledger.ledger import Ledger        # type: ignore
    from coherenceledger.keystore import KeyStore    # type: ignore
    from coherenceledger.crypto import b64encode     # type: ignore

    ledger = Ledger(path=ledger_path)
    ks = KeyStore(path=keystore_path)
    did, kp = ks.load_keypair()

    payload: Dict[str, Any] = {
        "artifact_type": "ucc.vote_guardrail",
        "manifest_id": manifest_id,
        "manifest_sha256": manifest_sha256,
        "audit_bundle_path": _safe_relpath(audit_bundle_path, repo_root),
        "audit_bundle_sha256": _sha256_file(audit_bundle_path),
        "report_path": _safe_relpath(report_path, repo_root),
        "report_sha256": _sha256_file(report_path),
    }

    ev = LedgerEvent.create_unsigned(
        actor_did=did.did,
        purpose=purpose,
        event_type="ucc.vote_guardrail.anchor",
        payload=payload,
        prev_seal=ledger.last_seal(),
    )
    sig = kp.sign(ev.signing_payload())
    ev.signature = b64encode(sig)
    ev.public_key_b64 = b64encode(kp.public_bytes_raw())

    ledger.append(ev)
    ledger.verify()
    return {"event_id": ev.event_id, "seal": ev.seal}


def write_guardrail(
    *,
    outdir: Path,
    manifest_path: Path,
    strict: bool = False,
    sign: bool = False,
    anchor: bool = False,
    repo_root: Optional[Path] = None,
    keystore_path: Optional[Path] = None,
    ledger_path: Optional[Path] = None,
    ledger_purpose: str = "ucc.vote_guardrail.anchor",
) -> Dict[str, Path]:
    """
    Writes:
      outdir/guardrail/report.json
      outdir/guardrail/audit_bundle.json
    Optionally signs report and anchors bundle+report into ledger.
    """
    outdir = outdir.resolve()
    gdir = outdir / "guardrail"
    gdir.mkdir(parents=True, exist_ok=True)

    repo_root = repo_root.resolve() if repo_root else None
    if repo_root is None:
        repo_root = Path(__file__).resolve().parents[3]

    keystore_path = (keystore_path or (repo_root / ".secrets" / "coherenceledger_keystore.json")).resolve()
    ledger_path = (ledger_path or (repo_root / "ledger.jsonl")).resolve()

    manifest = load_manifest(manifest_path)
    m_sha = _sha256_file(manifest_path)
    report = audit_vote_manifest(manifest, manifest_sha256=m_sha, strict=strict)

    if sign:
        _sign_inplace(report, keystore_path=keystore_path)

    report_path = gdir / "report.json"
    report_path.write_text(
        json.dumps(report, ensure_ascii=False, separators=(",", ":"), sort_keys=True),
        encoding="utf-8",
    )

    bundle = {
        "version": 1,
        "schema_id": "ucc.audit_bundle.v1",
        "created_at": _utc_now_iso(),
        "artifact": "vote_guardrail",
        "manifest_id": manifest.get("manifest_id"),
        "manifest_path": _safe_relpath(manifest_path, repo_root),
        "manifest_sha256": m_sha,
        "report_path": "guardrail/report.json",
        "report_sha256": _sha256_file(report_path),
        "passed": report.get("passed", False),
        "violations": len(report.get("violations", [])),
        "warnings": len(report.get("warnings", [])),
    }

    audit_bundle_path = gdir / "audit_bundle.json"
    audit_bundle_path.write_text(
        json.dumps(bundle, ensure_ascii=False, separators=(",", ":"), sort_keys=True),
        encoding="utf-8",
    )

    if anchor:
        _anchor_guardrail_bundle(
            audit_bundle_path=audit_bundle_path,
            report_path=report_path,
            manifest_id=str(manifest.get("manifest_id")),
            manifest_sha256=m_sha,
            ledger_path=ledger_path,
            keystore_path=keystore_path,
            repo_root=repo_root,
            purpose=ledger_purpose,
        )

    return {"report": report_path, "audit_bundle": audit_bundle_path}


def ensure_guardrail_passed(
    *,
    outdir: Path,
    manifest_path: Path,
    strict: bool = False,
    allow_cached: bool = True,
) -> bool:
    """
    Enforce gate:
      - if cached guardrail/report.json exists for the same manifest_sha256 and passed==true, OK
      - else rerun guardrail; if pass -> OK else FAIL
    """
    outdir = outdir.resolve()
    g_report = outdir / "guardrail" / "report.json"
    m_sha = _sha256_file(manifest_path)

    if allow_cached and g_report.exists():
        try:
            rep = json.loads(g_report.read_text(encoding="utf-8-sig"))
            if rep.get("manifest_sha256") == m_sha and rep.get("passed") is True:
                return True
        except Exception:
            pass

    # rerun guardrail; anchor if ledger enabled
    enable_ledger = _truthy_env("COHERENCELEDGER_ENABLE")
    write_guardrail(
        outdir=outdir,
        manifest_path=manifest_path,
        strict=strict,
        sign=enable_ledger,
        anchor=enable_ledger,
        ledger_purpose=os.getenv("COHERENCELEDGER_PURPOSE", "ucc.vote_guardrail.anchor"),
    )

    rep = json.loads((outdir / "guardrail" / "report.json").read_text(encoding="utf-8-sig"))
    return rep.get("passed") is True
