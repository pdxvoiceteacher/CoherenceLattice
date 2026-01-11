from __future__ import annotations

from pathlib import Path
from typing import Any, Dict, List
import json


class PublicOutputError(ValueError):
    pass


def load_public_values(public_json_path: Path) -> List[str]:
    """
    snarkjs public.json is typically a JSON array.
    We tolerate:
      - list: ["v1","v2",...]
      - dict with "values": {"values":[...]}
    """
    obj = json.loads(public_json_path.read_text(encoding="utf-8-sig"))

    if isinstance(obj, list):
        return [str(x) for x in obj]

    if isinstance(obj, dict) and isinstance(obj.get("values"), list):
        return [str(x) for x in obj["values"]]

    raise PublicOutputError("public.json must be a JSON array (or object with a 'values' array)")


def map_public_values(order: List[str], values: List[str]) -> Dict[str, str]:
    if not isinstance(order, list) or not all(isinstance(k, str) and k for k in order):
        raise PublicOutputError("order must be list[str]")
    if len(values) < len(order):
        raise PublicOutputError(f"public.json has {len(values)} values but order expects {len(order)}")
    return {k: str(values[i]) for i, k in enumerate(order)}


def public_signals_from_public_json(public_json_path: Path, order: List[str]) -> Dict[str, str]:
    vals = load_public_values(public_json_path)
    return map_public_values(order, vals)
