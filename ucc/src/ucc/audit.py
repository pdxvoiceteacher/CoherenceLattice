from __future__ import annotations

import hashlib
import json
import platform
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional


def sha256_bytes(b: bytes) -> str:
    h = hashlib.sha256()
    h.update(b)
    return h.hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def now_utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def git_commit() -> Optional[str]:
    try:
        out = subprocess.check_output(["git", "rev-parse", "HEAD"], stderr=subprocess.DEVNULL)
        return out.decode("utf-8", errors="replace").strip()
    except Exception:
        return None


@dataclass
class AuditBundle:
    bundle_version: str
    timestamp_utc: str
    module_id: str
    module_version: str
    module_path: str
    module_sha256: str
    input_path: str
    input_sha256: str
    outputs: Dict[str, str]   # name -> sha256
    metrics: Dict[str, Any]
    flags: Dict[str, Any]
    environment: Dict[str, Any]
    notes: Dict[str, Any]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "bundle_version": self.bundle_version,
            "timestamp_utc": self.timestamp_utc,
            "module": {
                "id": self.module_id,
                "version": self.module_version,
                "path": self.module_path,
                "sha256": self.module_sha256,
            },
            "input": {
                "path": self.input_path,
                "sha256": self.input_sha256,
            },
            "outputs": self.outputs,
            "metrics": self.metrics,
            "flags": self.flags,
            "environment": self.environment,
            "notes": self.notes,
        }


def write_bundle(outdir: Path, bundle: AuditBundle) -> Path:
    outdir.mkdir(parents=True, exist_ok=True)
    path = outdir / "audit_bundle.json"
    path.write_text(json.dumps(bundle.to_dict(), indent=2, sort_keys=True), encoding="utf-8")

    # COHERENCELEDGER_AUTOSEAL: optional ledger anchoring (env-gated, cross-platform)
    import os
    if os.getenv("COHERENCELEDGER_ENABLE", "").lower() in {"1","true","yes"}:
        strict = os.getenv("COHERENCELEDGER_STRICT", "").lower() in {"1","true","yes"}
        try:
            from pathlib import Path
            from coherenceledger.anchor import anchor_ucc_audit_bundle
        except Exception as e:
            if strict:
                raise
            try:
                import logging
                logging.getLogger(__name__).warning("coherenceledger unavailable; skipping auto-seal: %s", e)
            except Exception:
                pass
        else:
            # repo root inferred from this file's location: CoherenceLattice/ucc/src/ucc/audit.py
            repo_root = Path(__file__).resolve().parents[3]
            keystore = Path(os.getenv(
                "COHERENCELEDGER_KEYSTORE",
                str(repo_root / ".secrets" / "coherenceledger_keystore.json")
            ))
            ledger = Path(os.getenv(
                "COHERENCELEDGER_LEDGER",
                str(repo_root / "ledger.jsonl")
            ))
            purpose = os.getenv("COHERENCELEDGER_PURPOSE", "ucc.audit.anchor")

            if not keystore.exists():
                if strict:
                    raise FileNotFoundError(f"CoherenceLedger keystore not found: {keystore}")
                try:
                    import logging
                    logging.getLogger(__name__).warning("CoherenceLedger keystore missing; skipping auto-seal: %s", keystore)
                except Exception:
                    pass
            else:
                try:
                    ledger.parent.mkdir(parents=True, exist_ok=True)
                    report_path = outdir / "report.json"
                    report_arg = report_path if report_path.exists() else None
                    # 'path' is the audit_bundle.json path in this function
                    anchor_ucc_audit_bundle(
                        ledger_path=ledger,
                        keystore_path=keystore,
                        audit_bundle_path=path,
                        report_json_path=report_arg,
                        repo_root=repo_root,
                        purpose=purpose,
                    )
                except Exception as e:
                    if strict:
                        raise
                    try:
                        import logging
                        logging.getLogger(__name__).warning("CoherenceLedger auto-seal failed; continuing: %s", e)
                    except Exception:
                        pass

    return path


def env_info() -> Dict[str, Any]:
    return {
        "python_version": sys.version,
        "platform": platform.platform(),
        "git_commit": git_commit(),
    }
