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
    return path


def env_info() -> Dict[str, Any]:
    return {
        "python_version": sys.version,
        "platform": platform.platform(),
        "git_commit": git_commit(),
    }
