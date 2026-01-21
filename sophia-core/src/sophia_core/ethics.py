from __future__ import annotations

from typing import Dict


def compute_es(metrics: Dict[str, float]) -> float:
    compassion = float(metrics.get("E", 0.0))
    capability_growth = float(metrics.get("DeltaS", 0.0))
    denominator = 1.0 + max(0.0, capability_growth)
    if denominator == 0.0:
        return 0.0
    return compassion / denominator
