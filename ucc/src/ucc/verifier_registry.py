from __future__ import annotations

"""
Verifier Registry v0.7

Loads verifier specs from:
1) committed file: ucc/verifiers/registry.json (authoritative)
2) optional extra registry: env UCC_VERIFIER_REGISTRY_PATH (overlay)
3) built-in DEFAULT_REGISTRY fallback (for dev)

Supports vk pinning:
- spec may include vk_path + vk_sha256 + pin_required
"""

from pathlib import Path
from typing import Any, Dict, Optional
import json
import os


DEFAULT_VERIFIER_ID = "stub.sha256.v1"

DEFAULT_REGISTRY: Dict[str, Dict[str, Any]] = {
    "stub.sha256.v1": {
        "kind": "stub",
        "alg": "PROOF_STUB_SHA256",
        "enabled": True,
        "vk_path": None,
        "vk_sha256": None,
        "pin_required": False,
    }
}


def _read_json(path: Path) -> Optional[dict]:
    try:
        return json.loads(path.read_text(encoding="utf-8-sig"))
    except Exception:
        return None


def load_registry(extra_path: Optional[Path] = None) -> Dict[str, Dict[str, Any]]:
    # Start from built-in fallback
    reg = dict(DEFAULT_REGISTRY)

    # Merge committed registry if present
    repo_root = Path(__file__).resolve().parents[3]
    committed = repo_root / "ucc" / "verifiers" / "registry.json"
    obj = _read_json(committed)
    if isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(k, str) and isinstance(v, dict):
                reg[k] = v

    # Merge env overlay if present
    p = extra_path
    if p is None:
        envp = os.getenv("UCC_VERIFIER_REGISTRY_PATH", "").strip()
        p = Path(envp) if envp else None

    if p and p.exists():
        obj2 = _read_json(p)
        if isinstance(obj2, dict):
            for k, v in obj2.items():
                if isinstance(k, str) and isinstance(v, dict):
                    reg[k] = v

    return reg


def get_spec(verifier_id: str, registry: Optional[Dict[str, Dict[str, Any]]] = None) -> Dict[str, Any]:
    registry = registry or load_registry()
    spec = registry.get(verifier_id)
    if not spec:
        raise ValueError(f"Unknown verifier_id: {verifier_id}")
    if not spec.get("enabled", True):
        raise ValueError(f"Verifier disabled: {verifier_id}")
    return spec


def resolve_vk_path(spec: Dict[str, Any]) -> Optional[Path]:
    p = spec.get("vk_path")
    if not p:
        return None
    repo_root = Path(__file__).resolve().parents[3]
    return (repo_root / str(p)).resolve()
