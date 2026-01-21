from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, Tuple


def _load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _save_json(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8")


def update_kernel(history_path: Path, metrics: Dict[str, float], alpha: float) -> Dict[str, float]:
    kernel = {}
    if history_path.exists():
        try:
            kernel = _load_json(history_path)
        except json.JSONDecodeError:
            kernel = {}

    updated = dict(kernel)
    for key in ("Psi", "Lambda"):
        if key not in metrics:
            continue
        current = float(metrics[key])
        prev = float(kernel.get(key, current))
        updated[key] = prev * (1.0 - alpha) + current * alpha

    _save_json(history_path, updated)
    return updated


def detect_drift(kernel: Dict[str, float], metrics: Dict[str, float], thresholds: Dict[str, float]) -> Tuple[bool, Dict[str, float]]:
    deltas: Dict[str, float] = {}
    drift = False
    for key in ("Psi", "Lambda"):
        if key not in metrics or key not in kernel:
            continue
        delta = float(metrics[key]) - float(kernel[key])
        deltas[key] = delta
        limit = float(thresholds.get(key, 0.0))
        if abs(delta) >= limit and limit > 0:
            drift = True
    return drift, deltas
