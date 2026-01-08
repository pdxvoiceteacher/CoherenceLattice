from __future__ import annotations

from pathlib import Path
from typing import Any, Dict, Optional
import hashlib
import json


class CircuitRegistryError(ValueError):
    pass


def _sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def _read_json(path: Path) -> Optional[dict]:
    try:
        return json.loads(path.read_text(encoding="utf-8-sig"))
    except Exception:
        return None


def load_circuit_registry() -> Dict[str, Dict[str, Any]]:
    repo_root = Path(__file__).resolve().parents[3]
    reg_path = repo_root / "ucc" / "circuits" / "registry.json"
    obj = _read_json(reg_path)
    if not isinstance(obj, dict):
        raise CircuitRegistryError(f"Missing or invalid circuit registry: {reg_path}")
    return obj


def resolve_circuit_path(spec: Dict[str, Any]) -> Optional[Path]:
    p = spec.get("circuit_path")
    if not p:
        return None
    pth = Path(str(p))
    if pth.is_absolute():
        return pth
    repo_root = Path(__file__).resolve().parents[3]
    return (repo_root / pth).resolve()


def get_circuit_spec(circuit_id: str, reg: Optional[Dict[str, Dict[str, Any]]] = None) -> Dict[str, Any]:
    reg = reg or load_circuit_registry()
    spec = reg.get(circuit_id)
    if not spec:
        raise CircuitRegistryError(f"Unknown circuit_id: {circuit_id}")
    if not spec.get("enabled", True):
        raise CircuitRegistryError(f"Circuit disabled: {circuit_id}")
    return spec


def load_and_pin_circuit_descriptor(circuit_id: str) -> Dict[str, Any]:
    reg = load_circuit_registry()
    spec = get_circuit_spec(circuit_id, reg)
    path = resolve_circuit_path(spec)
    if not path or not path.exists():
        raise CircuitRegistryError(f"circuit_path missing or not found for {circuit_id}: {path}")

    b = path.read_bytes()
    actual = _sha256_hex(b)
    expected = spec.get("circuit_sha256")
    if expected and str(actual) != str(expected):
        raise CircuitRegistryError("circuit_sha256 mismatch (circuit pin violated)")

    obj = json.loads(b.decode("utf-8-sig"))
    return {"spec": spec, "descriptor": obj, "path": str(path), "sha256": actual}
