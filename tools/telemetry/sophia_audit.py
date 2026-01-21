#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib
import importlib.util
import json
import os
from pathlib import Path
from typing import Any, Dict, List

_run_audit_v3 = None
_run_audit_v2 = None
_run_basic_audit = None
if importlib.util.find_spec("sophia_core.audit") is not None:
    from sophia_core.audit import run_audit_v3 as _run_audit_v3
    from sophia_core.audit import run_audit_v2 as _run_audit_v2
    from sophia_core.audit import run_basic_audit as _run_basic_audit

from jsonschema import Draft202012Validator


def load_json(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-dir", required=True, help="Run directory containing telemetry.json and epistemic_graph.json")
    ap.add_argument("--repo-root", default=".")
    ap.add_argument("--diff-report", default="", help="Optional guidance_diff report.json")
    ap.add_argument("--schema", default="schema/sophia_audit_v3.schema.json")
    ap.add_argument(
        "--audit-sophia",
        action="store_true",
        help="Emit Sophia TEL events to <run-dir>/ucc_tel_events.jsonl.",
    )
    ap.add_argument("--audit-config", default="", help="Optional Sophia audit config JSON path.")
    ap.add_argument("--blockchain-commit", action="store_true", help="Anchor the audit report hash to a ledger.")
    ap.add_argument("--calibrate-trajectories", action="store_true", help="Enable trajectory phase checks.")
    ap.add_argument("--ethics-check", action="store_true", help="Enable ethical symmetry checks.")
    ap.add_argument("--memory-aware", action="store_true", help="Enable causal memory drift checks.")
    ap.add_argument("--out", default="", help="Output path (default: <run-dir>/sophia_audit.json)")
    args = ap.parse_args()

    repo = Path(args.repo_root).resolve()
    run_dir = Path(args.run_dir).resolve()
    run_basic_audit = _run_basic_audit
    run_audit_v2 = _run_audit_v2
    run_audit_v3 = _run_audit_v3

    if run_basic_audit is None:
        sophia_src = repo / "sophia-core" / "src"
        if sophia_src.exists():
            import sys

            sys.path.insert(0, str(sophia_src))
            if importlib.util.find_spec("sophia_core.audit") is not None:
                module = importlib.import_module("sophia_core.audit")
                run_audit_v3 = getattr(module, "run_audit_v3", None)
                run_audit_v2 = getattr(module, "run_audit_v2", None)
                run_basic_audit = getattr(module, "run_basic_audit", None)
            else:
                run_audit_v3 = None
                run_audit_v2 = None
                run_basic_audit = None

    tele = load_json(run_dir / "telemetry.json")
    graph = load_json(run_dir / "epistemic_graph.json")

    if args.audit_sophia:
        os.environ.setdefault("UCC_TEL_EVENTS_OUT", str(run_dir / "ucc_tel_events.jsonl"))

    # Build artifact set from graph nodes
    artifacts = set()
    for n in graph.get("nodes", []):
        if n.get("kind") == "artifact":
            p = (n.get("data") or {}).get("path")
            if p:
                artifacts.add(str(p).replace("\\", "/"))

    findings: List[Dict[str, Any]] = []
    repairs: List[Dict[str, Any]] = []
    trend_summary: Dict[str, Any] = {}
    contradictions: List[Dict[str, Any]] = []
    repair_suggestions: List[Dict[str, Any]] = []
    metrics_snapshot: Dict[str, Any] = {}
    trajectory_phase = "unknown"
    ethical_symmetry: Any = None
    memory_kernel: Dict[str, Any] = {}
    memory_drift_flag = False
    blockchain_anchor_hash = None

    audit_config_path = Path(args.audit_config).resolve() if args.audit_config else None

    if run_audit_v3 is not None:
        audit = run_audit_v3(
            tele,
            graph,
            repo_root=repo,
            audit_config_path=audit_config_path,
            tel_hook=None,
            emit_repair_events=args.audit_sophia,
            calibrate_trajectories=args.calibrate_trajectories,
            ethics_check=args.ethics_check,
            memory_aware=args.memory_aware,
        )
        findings = [
            {
                "id": f.id,
                "severity": f.severity,
                "type": f.type,
                "message": f.message,
                "data": f.data,
            }
            for f in audit.findings
        ]
        repairs = [
            {
                "id": r.id,
                "priority": r.priority,
                "action": r.action,
                "details": r.details,
            }
            for r in audit.repairs
        ]
        trend_summary = audit.trend_summary
        contradictions = [
            {"statements": c.statements, "kind": c.kind, "key": c.key} for c in audit.contradictions
        ]
        repair_suggestions = [
            {
                "id": s.id,
                "priority": s.priority,
                "suggestion": s.suggestion,
                "reason": s.reason,
                "target_module": s.target_module,
                "target_file": s.target_file,
                "justification": s.justification,
            }
            for s in audit.repair_suggestions
        ]
        metrics_snapshot = audit.metrics_snapshot
        trajectory_phase = audit.trajectory_phase
        ethical_symmetry = audit.ethical_symmetry
        memory_kernel = audit.memory_kernel
        memory_drift_flag = audit.memory_drift_flag
    elif run_audit_v2 is not None:
        audit = run_audit_v2(
            tele,
            graph,
            repo_root=repo,
            audit_config_path=audit_config_path,
            tel_hook=None,
            emit_repair_events=args.audit_sophia,
        )
        findings = [
            {
                "id": f.id,
                "severity": f.severity,
                "type": f.type,
                "message": f.message,
                "data": f.data,
            }
            for f in audit.findings
        ]
        repairs = [
            {
                "id": r.id,
                "priority": r.priority,
                "action": r.action,
                "details": r.details,
            }
            for r in audit.repairs
        ]
        trend_summary = audit.trend_summary
        contradictions = [
            {"statements": c.statements, "kind": c.kind, "key": c.key} for c in audit.contradictions
        ]
        repair_suggestions = [
            {
                "id": s.id,
                "priority": s.priority,
                "suggestion": s.suggestion,
                "reason": s.reason,
                "target_module": s.target_module,
                "target_file": s.target_file,
                "justification": s.justification,
            }
            for s in audit.repair_suggestions
        ]
    elif run_basic_audit is not None:
        audit = run_basic_audit(tele, graph)
        findings = [
            {
                "id": f.id,
                "severity": f.severity,
                "type": f.type,
                "message": f.message,
                "data": f.data,
            }
            for f in audit.findings
        ]
        repairs = [
            {
                "id": r.id,
                "priority": r.priority,
                "action": r.action,
                "details": r.details,
            }
            for r in audit.repairs
        ]
    else:
        claims = tele.get("claims") or []

        # 1) Evidence integrity
        for c in claims:
            cid = c.get("id", "unknown")
            for ev in c.get("evidence", []) or []:
                evp = str(ev).replace("\\", "/")
                if evp not in artifacts:
                    findings.append({
                        "id": f"finding_missing_evidence_{cid}",
                        "severity": "fail",
                        "type": "missing_evidence",
                        "message": f"Claim {cid} references evidence not present in graph artifacts: {evp}",
                        "data": {"claim_id": cid, "evidence": evp}
                    })
                    repairs.append({
                        "id": f"repair_add_artifact_{cid}",
                        "priority": "high",
                        "action": "Ensure evidence paths are included in telemetry.artifacts and epistemic graph artifact nodes.",
                        "details": {"missing_evidence": evp}
                    })

        # 2) Counterevidence expectation
        for c in claims:
            ctype = c.get("type")
            conf = float(c.get("confidence", 0.0))
            if ctype in ("causal", "predictive") and conf >= 0.7:
                if not (c.get("counterevidence") or []):
                    cid = c.get("id", "unknown")
                    findings.append({
                        "id": f"finding_missing_counter_{cid}",
                        "severity": "warn",
                        "type": "missing_counterevidence",
                        "message": f"Claim {cid} is {ctype} with confidence {conf:.2f} but has no counterevidence listed.",
                        "data": {"claim_id": cid, "confidence": conf}
                    })
                    repairs.append({
                        "id": f"repair_add_counter_{cid}",
                        "priority": "medium",
                        "action": "Add at least one counterevidence path or reduce confidence / add assumptions.",
                        "details": {"claim_id": cid}
                    })

    # 3) Optional guidance diff tradeoff warning
    if args.diff_report:
        dr = load_json(Path(args.diff_report))
        d = dr.get("deltas", {})
        dPsi = float(d.get("Psi", 0.0))
        dLam = float(d.get("Lambda", 0.0))
        dDS = float(d.get("DeltaS", 0.0))
        if (dLam > 0 or dDS > 0) and abs(dPsi) < 1e-4:
            findings.append({
                "id": "finding_guidance_tradeoff",
                "severity": "warn",
                "type": "telemetry_regression_risk",
                "message": "Guided run increased DeltaS/Lambda while Psi gain is small; consider whether guidance adds instability.",
                "data": {"dPsi": dPsi, "dLambda": dLam, "dDeltaS": dDS}
            })
            repairs.append({
                "id": "repair_review_guidance",
                "priority": "medium",
                "action": "Review guidance knobs; prefer changes that do not increase DeltaS/Lambda unless Psi gain justifies tradeoff.",
                "details": None
            })

    # Decision
    decision = "pass"
    if any(f["severity"] == "fail" for f in findings):
        decision = "fail"
    elif any(f["severity"] == "warn" for f in findings):
        decision = "warn"

    schema_name = Path(args.schema).name
    if "v3" in schema_name:
        schema_id = "sophia_audit_v3"
    elif "v2" in schema_name:
        schema_id = "sophia_audit_v2"
    else:
        schema_id = "sophia_audit_v1"

    report = {
        "schema": schema_id,
        "run_id": tele.get("run_id", run_dir.name),
        "decision": decision,
        "summary": f"Sophia audit complete: {decision}. Findings={len(findings)} Repairs={len(repairs)}",
        "findings": findings,
        "repairs": repairs,
    }

    if schema_id == "sophia_audit_v2":
        report.update(
            {
                "trend_summary": trend_summary,
                "contradictions": contradictions,
                "repair_suggestions": repair_suggestions,
            }
        )
    if schema_id == "sophia_audit_v3":
        report.update(
            {
                "metrics_snapshot": metrics_snapshot,
                "trend_summary": trend_summary,
                "contradictions": contradictions,
                "repair_suggestions": repair_suggestions,
                "trajectory_phase": trajectory_phase,
                "ethical_symmetry": ethical_symmetry,
                "memory_kernel": memory_kernel,
                "memory_drift_flag": memory_drift_flag,
                "blockchain_anchor_hash": blockchain_anchor_hash,
            }
        )

    outp = Path(args.out) if args.out else (run_dir / "sophia_audit.json")
    if args.blockchain_commit and schema_id == "sophia_audit_v3":
        from tools.telemetry.blockchain_anchor import anchor_report

        ledger_path = repo / "runs" / "history" / "blockchain_anchors.jsonl"
        blockchain_anchor_hash = anchor_report(report, ledger_path)
        report["blockchain_anchor_hash"] = blockchain_anchor_hash

    outp.write_text(json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n")

    # Validate schema
    schema = load_json(repo / args.schema)
    Draft202012Validator(schema).validate(report)

    print(f"[sophia_audit] OK wrote {outp} decision={decision}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
