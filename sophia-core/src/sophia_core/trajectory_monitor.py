from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, Optional


def load_bounds(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def evaluate_phase(metrics: Dict[str, float], bounds: Dict[str, Any]) -> str:
    psi = metrics.get("Psi")
    lam = metrics.get("Lambda")
    if psi is None or lam is None:
        return "unknown"

    psi_cfg = bounds.get("Psi", {})
    lam_cfg = bounds.get("Lambda", {})

    psi_critical_min = psi_cfg.get("critical_min", 0.5)
    psi_warning_min = psi_cfg.get("warning_min", 0.6)
    lam_warning_max = lam_cfg.get("warning_max", 0.6)
    lam_critical_max = lam_cfg.get("critical_max", 0.8)

    if psi < psi_critical_min or lam > lam_critical_max:
        return "critical"
    if psi < psi_warning_min or lam > lam_warning_max:
        return "warning"
    return "stable"


def determine_phase(metrics: Dict[str, float], bounds_path: Optional[Path]) -> str:
    if bounds_path is None or not bounds_path.exists():
        return "unknown"
    bounds = load_bounds(bounds_path)
    return evaluate_phase(metrics, bounds)
