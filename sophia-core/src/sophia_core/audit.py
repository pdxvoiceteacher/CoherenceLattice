from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional

import json

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


@dataclass(frozen=True)
class Contradiction:
    statements: List[str]
    kind: str
    key: str


@dataclass(frozen=True)
class RepairSuggestion:
    id: str
    priority: str
    suggestion: str
    reason: str
    target_module: str
    target_file: str
    justification: Optional[str] = None


@dataclass(frozen=True)
class AuditReportV2:
    decision: str
    findings: List[Finding] = field(default_factory=list)
    repairs: List[Repair] = field(default_factory=list)
    trend_summary: Dict[str, Any] = field(default_factory=dict)
    contradictions: List[Contradiction] = field(default_factory=list)
    repair_suggestions: List[RepairSuggestion] = field(default_factory=list)


DEFAULT_THRESHOLDS = {
    "Psi_drop_warn": 0.05,
    "Lambda_spike_warn": 0.08,
}


def _load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _save_json(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8")


def load_audit_config(repo_root: Path, config_path: Optional[Path] = None) -> Dict[str, Any]:
    if config_path is None:
        config_path = repo_root / "sophia-core" / "config" / "audit_config.json"
    if config_path.exists():
        return _load_json(config_path)
    return {"thresholds": dict(DEFAULT_THRESHOLDS)}


def _metric_map(metrics: Mapping[str, Any]) -> Dict[str, float]:
    values = {}
    for key in ("Psi", "E", "T", "DeltaS", "Lambda", "Es"):
        if key in metrics:
            try:
                values[key] = float(metrics[key])
            except (TypeError, ValueError):
                continue
    return values


def _update_history(history_path: Path, run_id: str, metrics: Dict[str, float]) -> Dict[str, Any]:
    history = {"runs": {}, "summary": {"count": 0, "last": {}, "moving_avg": {}}}
    if history_path.exists():
        try:
            history = _load_json(history_path)
        except json.JSONDecodeError:
            history = {"runs": {}, "summary": {"count": 0, "last": {}, "moving_avg": {}}}

    runs = history.setdefault("runs", {})
    summary = history.setdefault("summary", {"count": 0, "last": {}, "moving_avg": {}})
    count = int(summary.get("count", 0))
    last = summary.get("last", {}) or {}
    moving_avg = summary.get("moving_avg", {}) or {}

    trends: Dict[str, Any] = {"history_count": count}
    for metric, value in metrics.items():
        prev_last = last.get(metric)
        prev_avg = moving_avg.get(metric)
        if prev_last is not None:
            trends[f"{metric}_delta"] = float(value) - float(prev_last)
            trends[f"{metric}_last"] = float(prev_last)
        if prev_avg is not None:
            new_avg = float(prev_avg) * 0.8 + float(value) * 0.2
        else:
            new_avg = float(value)
        moving_avg[metric] = new_avg
        trends[f"{metric}_moving_avg"] = round(new_avg, 4)
        last[metric] = float(value)

    summary["count"] = count + 1
    summary["last"] = last
    summary["moving_avg"] = moving_avg
    runs[run_id] = metrics
    _save_json(history_path, history)
    return trends


def _detect_negation(statement: str) -> bool:
    lowered = statement.lower()
    return (
        lowered.startswith("not ")
        or lowered.startswith("no ")
        or " not " in lowered
        or " never " in lowered
        or " no " in lowered
    )


def _normalize_statement(statement: str) -> str:
    lowered = statement.lower()
    for token in (" not ", " never ", " no "):
        lowered = lowered.replace(token, " ")
    return " ".join("".join(ch for ch in lowered if ch.isalnum() or ch.isspace()).split())


def detect_contradictions(claims: Iterable[Mapping[str, Any]]) -> List[Contradiction]:
    contradictions: List[Contradiction] = []
    seen: Dict[str, Dict[str, Any]] = {}
    for claim in claims:
        statement = str(claim.get("statement", "")).strip()
        if not statement:
            continue
        key = _normalize_statement(statement)
        if not key:
            continue
        polarity = not _detect_negation(statement)
        if key in seen:
            if seen[key]["polarity"] != polarity:
                contradictions.append(
                    Contradiction(
                        statements=[seen[key]["statement"], statement],
                        kind="DirectNegation",
                        key=key,
                    )
                )
        else:
            seen[key] = {"polarity": polarity, "statement": statement}
    return contradictions


def _build_repair_suggestions(
    findings: List[Finding],
    trend_summary: Dict[str, Any],
) -> List[RepairSuggestion]:
    suggestions: List[RepairSuggestion] = []
    evidence_fails = [f for f in findings if f.type == "missing_evidence"]
    if evidence_fails:
        suggestions.append(
            RepairSuggestion(
                id="suggestion_evidence_registry",
                priority="high",
                suggestion="Increase enforcement for evidence registration in telemetry artifacts.",
                reason=f"{len(evidence_fails)} missing evidence findings detected in this run.",
                target_module="unknown",
                target_file="unknown",
                justification="Evidence enforcement module not specified in telemetry.",
            )
        )

    psi_delta = trend_summary.get("Psi_delta")
    if isinstance(psi_delta, (int, float)) and psi_delta < 0:
        suggestions.append(
            RepairSuggestion(
                id="suggestion_review_coherence_controls",
                priority="medium",
                suggestion="Review coherence controls and guidance thresholds to prevent Ψ regression.",
                reason=f"Ψ decreased by {psi_delta:.3f} from the previous run.",
                target_module="UCC.Telemetry.GuidanceValidator",
                target_file="unknown",
                justification="Guidance validator is the closest known control surface for coherence drift.",
            )
        )
    return suggestions


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


def run_audit_v2(
    telemetry: Mapping[str, Any],
    epistemic_graph: Mapping[str, Any],
    *,
    repo_root: Optional[Path] = None,
    audit_config_path: Optional[Path] = None,
    history_path: Optional[Path] = None,
    tel_hook: Optional[TelHook] = None,
    emit_repair_events: bool = False,
) -> AuditReportV2:
    base = run_basic_audit(telemetry, epistemic_graph, tel_hook=tel_hook)
    findings = list(base.findings)
    repairs = list(base.repairs)
    repo_root = repo_root or Path(".").resolve()
    config = load_audit_config(repo_root, audit_config_path)
    thresholds = config.get("thresholds", DEFAULT_THRESHOLDS)

    metrics = _metric_map(telemetry.get("metrics", {}) or {})
    run_id = str(telemetry.get("run_id", "unknown"))
    history_path = history_path or (repo_root / "runs" / "history" / "history_summary.json")
    trend_summary = _update_history(history_path, run_id, metrics) if metrics else {"history_count": 0}

    if metrics and trend_summary.get("history_count", 0) > 0:
        psi_delta = trend_summary.get("Psi_delta")
        if isinstance(psi_delta, (int, float)) and psi_delta <= -float(thresholds.get("Psi_drop_warn", 0.05)):
            findings.append(
                Finding(
                    id="finding_psi_regression",
                    severity="warn",
                    type="coherence_regression",
                    message=f"Psi dropped by {psi_delta:.3f} since last run.",
                    data={"Psi_delta": psi_delta},
                )
            )

        lambda_delta = trend_summary.get("Lambda_delta")
        if isinstance(lambda_delta, (int, float)) and lambda_delta >= float(
            thresholds.get("Lambda_spike_warn", 0.08)
        ):
            findings.append(
                Finding(
                    id="finding_lambda_spike",
                    severity="warn",
                    type="coherence_regression",
                    message=f"Lambda increased by {lambda_delta:.3f} since last run.",
                    data={"Lambda_delta": lambda_delta},
                )
            )

    claims = telemetry.get("claims") or []
    contradictions = detect_contradictions(claims)
    if contradictions:
        findings.append(
            Finding(
                id="finding_contradictions",
                severity="warn",
                type="contradiction",
                message=f"Detected {len(contradictions)} contradictory claim pairs.",
                data={"count": len(contradictions)},
            )
        )
    if not claims:
        emit_sophia_event(
            "sophia.contradiction.check",
            {"no_claims_available_for_contradiction_check": True, "meta": {"source": "sophia-core"}},
        )

    repair_suggestions = _build_repair_suggestions(findings, trend_summary)
    if emit_repair_events:
        for suggestion in repair_suggestions:
            emit_sophia_event(
                "sophia.repair.suggested",
                {
                    "target_module": suggestion.target_module,
                    "target_file": suggestion.target_file,
                    "suggestion": suggestion.suggestion,
                    "reason": suggestion.reason,
                    "priority": suggestion.priority,
                    "justification": suggestion.justification,
                    "meta": {"source": "sophia-core"},
                },
            )

    decision = base.decision
    if any(f.severity == "fail" for f in findings):
        decision = "fail"
    elif any(f.severity == "warn" for f in findings):
        decision = "warn"

    return AuditReportV2(
        decision=decision,
        findings=findings,
        repairs=repairs,
        trend_summary=trend_summary,
        contradictions=contradictions,
        repair_suggestions=repair_suggestions,
    )
