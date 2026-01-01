from __future__ import annotations

from dataclasses import dataclass
from typing import Dict

from .models import UCCModule


@dataclass
class EvaluationScores:
    """0–5 scores per evaluation dimension."""
    alignment: int
    robustness: int
    clarity: int
    safety_escalation: int
    usability: int
    governance: int

    def total(self) -> int:
        return (
            self.alignment
            + self.robustness
            + self.clarity
            + self.safety_escalation
            + self.usability
            + self.governance
        )


def empty_scores() -> EvaluationScores:
    return EvaluationScores(0, 0, 0, 0, 0, 0)


def to_dict(scores: EvaluationScores) -> Dict[str, int]:
    return {
        "alignment": scores.alignment,
        "robustness": scores.robustness,
        "clarity": scores.clarity,
        "safety_escalation": scores.safety_escalation,
        "usability": scores.usability,
        "governance": scores.governance,
        "total": scores.total(),
    }


def quick_heuristic_score(module: UCCModule) -> EvaluationScores:
    """
    Very rough heuristic scoring (v0.x).
    Intended as a helper/sanity-check, not certification.
    """
    scores = empty_scores()

    # Alignment
    if module.authorities and module.meta.domain and module.meta.jurisdiction:
        scores.alignment += 3
        if len(module.authorities) > 1:
            scores.alignment += 1

    # Robustness
    if module.validation_rules:
        scores.robustness += 2
        if module.evidence.min_primary_sources >= 3:
            scores.robustness += 1

    # Clarity
    if all(t.description for t in module.tasks):
        scores.clarity += 2
    if len(module.reporting.sections) >= 4:
        scores.clarity += 1

    # Safety & escalation
    if module.escalation_policy:
        scores.safety_escalation += 2
        if len(module.escalation_policy) > 1:
            scores.safety_escalation += 1

    # Usability
    if 3 <= len(module.reasoning_steps) <= 20:
        scores.usability += 2

    # Governance
    if module.meta.version.count(".") == 2 and "." in module.meta.module_id:
        scores.governance += 1

    # Clamp 0..5
    scores.alignment = min(scores.alignment, 5)
    scores.robustness = min(scores.robustness, 5)
    scores.clarity = min(scores.clarity, 5)
    scores.safety_escalation = min(scores.safety_escalation, 5)
    scores.usability = min(scores.usability, 5)
    scores.governance = min(scores.governance, 5)

    return scores