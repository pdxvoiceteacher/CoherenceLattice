from __future__ import annotations

import json
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Dict, List, Literal, Optional, Any

AuthorityType = Literal["law", "regulation", "standard", "guideline", "ethics", "policy"]

EscalationAction = Literal["request_more_info", "flag_for_review", "refuse"]


@dataclass
class AuthorityRef:
    """Reference to a governing authority (law, standard, guideline, etc.)."""
    type: AuthorityType
    id: str
    name: Optional[str] = None
    url: Optional[str] = None
    version: Optional[str] = None


@dataclass
class Task:
    """Human-facing task this module constrains."""
    id: str
    description: str


@dataclass
class EvidenceRequirements:
    """Evidence requirements for the reasoning process."""
    min_primary_sources: int = 0
    recency_years: Optional[int] = None
    require_trial_registry: bool = False
    hierarchy: List[str] = field(default_factory=list)


@dataclass
class ValidationRule:
    """
    A simple assertion the AI must check against its own output.
    v0.x keeps rules as strings; a richer DSL can come later.
    """
    id: str
    description: str
    expression: str


@dataclass
class ReportingStructure:
    """Required reporting layout."""
    sections: List[str] = field(default_factory=list)
    disclaimers: List[str] = field(default_factory=list)


@dataclass
class EscalationCondition:
    """When the AI must request info, flag for review, or refuse."""
    condition: str
    action: EscalationAction


@dataclass
class ModuleMetadata:
    """
    Top-level metadata about a UCC grammar module.
    Matches the Supplement’s “ModuleMetadata” concept (domain/jurisdiction/description).
    """
    module_id: str
    name: str
    version: str
    domain: List[str] = field(default_factory=list)
    jurisdiction: List[str] = field(default_factory=list)
    description: Optional[str] = None


@dataclass
class UCCModule:
    """
    Main UCC grammar module specification.

    meta: ModuleMetadata
    authorities: List[AuthorityRef]
    tasks: List[Task]
    roles: List[str]
    reasoning_steps: List[str]
    evidence: EvidenceRequirements
    validation_rules: List[ValidationRule]
    reporting: ReportingStructure
    escalation_policy: List[EscalationCondition]
    """
    meta: ModuleMetadata
    authorities: List[AuthorityRef]
    tasks: List[Task]
    roles: List[str]
    reasoning_steps: List[str]
    evidence: EvidenceRequirements
    validation_rules: List[ValidationRule]
    reporting: ReportingStructure
    escalation_policy: List[EscalationCondition]

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


def load_uccmodule_json(path: Path) -> UCCModule:
    """
    Load the typed UCC grammar module from a JSON file.

    NOTE: uses utf-8-sig to tolerate BOM on Windows editors.
    """
    data = json.loads(path.read_text(encoding="utf-8-sig"))
    return uccmodule_from_dict(data)


def uccmodule_from_dict(data: Dict[str, Any]) -> UCCModule:
    meta = ModuleMetadata(**data["meta"])
    authorities = [AuthorityRef(**a) for a in data.get("authorities", [])]
    tasks = [Task(**t) for t in data.get("tasks", [])]
    evidence = EvidenceRequirements(**data.get("evidence", {}))
    validation_rules = [ValidationRule(**r) for r in data.get("validation_rules", [])]
    reporting = ReportingStructure(**data.get("reporting", {}))
    escalation_policy = [EscalationCondition(**c) for c in data.get("escalation_policy", [])]

    return UCCModule(
        meta=meta,
        authorities=authorities,
        tasks=tasks,
        roles=list(data.get("roles", [])),
        reasoning_steps=list(data.get("reasoning_steps", [])),
        evidence=evidence,
        validation_rules=validation_rules,
        reporting=reporting,
        escalation_policy=escalation_policy,
    )