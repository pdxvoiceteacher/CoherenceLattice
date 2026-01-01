from __future__ import annotations

from typing import List

from .models import UCCModule


class ValidationError(Exception):
    """Raised when a UCC grammar module fails structural validation."""


def validate_basic_structure(module: UCCModule) -> None:
    """
    Lightweight structural checks (v0.x). Raises ValidationError if clearly wrong.
    Mirrors the Supplement’s “validate_basic_structure”.
    """
    if not module.meta.module_id:
        raise ValidationError("module.meta.module_id is required.")
    if not module.meta.version:
        raise ValidationError("module.meta.version is required.")
    if not module.reasoning_steps:
        raise ValidationError("At least one reasoning step is required.")
    if not module.tasks:
        raise ValidationError("At least one task is required.")
    if not module.authorities:
        raise ValidationError("At least one authority reference is required.")
    if not module.reporting.sections:
        raise ValidationError("Reporting structure must specify at least one section.")


def check_authority_alignment(module: UCCModule) -> List[str]:
    """
    Very simple alignment checks: warn if declared jurisdiction looks inconsistent
    with referenced authorities. Returns warnings; empty means no obvious issues.

    (Full legal/domain review still required.)
    """
    warnings: List[str] = []

    jurisdictions = set(j.lower() for j in module.meta.jurisdiction)
    authority_ids = [a.id.upper() for a in module.authorities]

    eu_markers = {"EU", "GDPR", "EU-AI-ACT"}
    us_markers = {"US", "USA", "HIPAA", "FERPA", "SEC", "FDA"}

    cites_eu = any(any(m in aid for m in eu_markers) for aid in authority_ids)
    cites_us = any(any(m in aid for m in us_markers) for aid in authority_ids)

    if "global" in jurisdictions and (cites_eu or cites_us):
        warnings.append(
            "Module declares 'global' jurisdiction but references region-specific authorities; "
            "consider scoping jurisdiction more narrowly or providing regional variants."
        )

    return warnings