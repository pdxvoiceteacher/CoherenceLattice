from __future__ import annotations

from pathlib import Path
from typing import Any, Dict, Optional
import hashlib
import json

from jsonschema import Draft202012Validator

from ucc.verifier_registry import resolve_signals_schema_path


class PublicSignalsSchemaError(ValueError):
    pass


def _sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def _load_schema_bytes(path: Path) -> bytes:
    return path.read_bytes()


def _load_schema_obj(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


_validator_cache: Dict[str, Draft202012Validator] = {}
_schema_sha_cache: Dict[str, str] = {}


def schema_sha256(path: Path) -> str:
    k = str(path.resolve())
    if k in _schema_sha_cache:
        return _schema_sha_cache[k]
    sha = _sha256_hex(_load_schema_bytes(path))
    _schema_sha_cache[k] = sha
    return sha


def _get_validator(path: Path) -> Draft202012Validator:
    k = str(path.resolve())
    if k in _validator_cache:
        return _validator_cache[k]
    obj = _load_schema_obj(path)
    Draft202012Validator.check_schema(obj)
    v = Draft202012Validator(obj)
    _validator_cache[k] = v
    return v


def validate_public_signals(public_signals: Dict[str, Any], verifier_spec: Dict[str, Any]) -> None:
    """
    Validates public_signals against the schema pinned in verifier_spec:
      - verifier_spec["signals_schema_path"]
      - verifier_spec["signals_schema_sha256"] (optional pin)
      - verifier_spec["signals_schema_required"] (optional)
    """
    required = bool(verifier_spec.get("signals_schema_required", False))
    path = resolve_signals_schema_path(verifier_spec)

    if not path:
        if required:
            raise PublicSignalsSchemaError("signals schema required but signals_schema_path not set in verifier spec")
        return

    if not path.exists():
        raise PublicSignalsSchemaError(f"signals schema file not found: {path}")

    expected_sha = verifier_spec.get("signals_schema_sha256")
    if expected_sha:
        actual = schema_sha256(path)
        if str(actual) != str(expected_sha):
            raise PublicSignalsSchemaError("signals_schema_sha256 mismatch (schema pin violated)")

    v = _get_validator(path)
    errs = sorted(v.iter_errors(public_signals), key=lambda e: e.path)
    if errs:
        e0 = errs[0]
        loc = ".".join(str(x) for x in e0.path) if e0.path else "<root>"
        raise PublicSignalsSchemaError(f"public_signals schema violation at {loc}: {e0.message}")
