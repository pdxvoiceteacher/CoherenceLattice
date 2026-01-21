from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Mapping, Optional

from sophia_core.tel import TelEvent, TelHook, emit_hook_event, emit_sophia_event


@dataclass(frozen=True)
class Finding:
    id: str
    severity: str
    type: str
    message: str
    data: Dict[str, Any]


@dataclass(frozen=True)
class Repair:
    id: str
    priority: str
    action: str
    details: Optional[Dict[str, Any]]


@dataclass(frozen=True)
class AuditResult:
    decision: str
    findings: List[Finding] = field(default_factory=list)
    repairs: List[Repair] = field(default_factory=list)


def run_basic_audit(
    telemetry: Mapping[str, Any],
    epistemic_graph: Mapping[str, Any],
    *,
    tel_hook: Optional[TelHook] = None,
) -> AuditResult:
    emit_sophia_event("sophia.audit.start", {"run_id": telemetry.get("run_id")})
    emit_hook_event(tel_hook, TelEvent("sophia.audit.start", {"run_id": telemetry.get("run_id")}))

    artifacts = set()
    for node in epistemic_graph.get("nodes", []):
        if node.get("kind") == "artifact":
            path = (node.get("data") or {}).get("path")
            if path:
                artifacts.add(str(path).replace("\\", "/"))

    findings: List[Finding] = []
    repairs: List[Repair] = []

    for claim in telemetry.get("claims") or []:
        claim_id = claim.get("id", "unknown")
        for evidence in claim.get("evidence", []) or []:
            evidence_path = str(evidence).replace("\\", "/")
            if evidence_path not in artifacts:
                findings.append(
                    Finding(
                        id=f"finding_missing_evidence_{claim_id}",
                        severity="fail",
                        type="missing_evidence",
                        message=(
                            "Claim references evidence not present in graph artifacts: "
                            f"{evidence_path}"
                        ),
                        data={"claim_id": claim_id, "evidence": evidence_path},
                    )
                )
                repairs.append(
                    Repair(
                        id=f"repair_add_artifact_{claim_id}",
                        priority="high",
                        action=(
                            "Ensure evidence paths are included in telemetry artifacts "
                            "and epistemic graph artifact nodes."
                        ),
                        details={"missing_evidence": evidence_path},
                    )
                )

    for claim in telemetry.get("claims") or []:
        claim_type = claim.get("type")
        confidence = float(claim.get("confidence", 0.0))
        if claim_type in ("causal", "predictive") and confidence >= 0.7:
            if not (claim.get("counterevidence") or []):
                claim_id = claim.get("id", "unknown")
                findings.append(
                    Finding(
                        id=f"finding_missing_counter_{claim_id}",
                        severity="warn",
                        type="missing_counterevidence",
                        message=(
                            "Claim is high-confidence without counterevidence: "
                            f"{claim_id}"
                        ),
                        data={"claim_id": claim_id, "confidence": confidence},
                    )
                )
                repairs.append(
                    Repair(
                        id=f"repair_add_counter_{claim_id}",
                        priority="medium",
                        action="Add counterevidence or reduce confidence.",
                        details={"claim_id": claim_id},
                    )
                )

    decision = "pass"
    if any(finding.severity == "fail" for finding in findings):
        decision = "fail"
    elif any(finding.severity == "warn" for finding in findings):
        decision = "warn"

    emit_sophia_event(
        "sophia.audit.end",
        {"run_id": telemetry.get("run_id"), "decision": decision},
    )
    emit_hook_event(
        tel_hook,
        TelEvent("sophia.audit.end", {"run_id": telemetry.get("run_id"), "decision": decision}),
    )

    return AuditResult(decision=decision, findings=findings, repairs=repairs)
