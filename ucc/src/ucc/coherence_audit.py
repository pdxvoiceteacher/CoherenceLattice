from __future__ import annotations

import csv
import json
import re
from pathlib import Path
from statistics import mean
from typing import Any, Dict, List, Optional, Tuple


_TOKEN_RE = re.compile(r"[a-z0-9]+(?:'[a-z0-9]+)?", re.IGNORECASE)


def tokenize(text: str) -> List[str]:
    """Lowercased word-ish tokens. Stable, dependency-free."""
    if not isinstance(text, str):
        return []
    return [t.lower() for t in _TOKEN_RE.findall(text)]


def jaccard_distance(tokens_a: List[str], tokens_b: List[str]) -> float:
    """1 - |A∩B|/|A∪B| ; returns 0 if both empty."""
    a = set(tokens_a)
    b = set(tokens_b)
    if not a and not b:
        return 0.0
    u = a | b
    i = a & b
    return 1.0 - (len(i) / max(len(u), 1))


def _as_list(x: Any) -> List[Any]:
    return x if isinstance(x, list) else []


def _as_dict(x: Any) -> Dict[str, Any]:
    return x if isinstance(x, dict) else {}


def _nonempty_str(x: Any) -> bool:
    return isinstance(x, str) and len(x.strip()) > 0


def _get_threshold(thresholds: Dict[str, Any], key: str, default: float) -> float:
    try:
        v = thresholds.get(key, default)
        return float(v)
    except Exception:
        return float(default)


def _mode_label(labels: List[str]) -> Optional[str]:
    if not labels:
        return None
    counts: Dict[str, int] = {}
    for s in labels:
        counts[s] = counts.get(s, 0) + 1
    return sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[0][0]


def _required_sections_coverage(
    artifact: Dict[str, Any], required: List[str]
) -> Tuple[List[str], List[str], List[str], float]:
    """
    A required section is present if:
      - artifact["sections"][name] is a nonempty string, OR
      - artifact[name] is a nonempty string (fallback).
    """
    sec = _as_dict(artifact.get("sections"))
    present: List[str] = []
    missing: List[str] = []

    for name in required:
        if _nonempty_str(sec.get(name)) or _nonempty_str(artifact.get(name)):
            present.append(name)
        else:
            missing.append(name)

    cov = (len(present) / len(required)) if required else 1.0
    return required, present, missing, float(cov)


def _claim_metrics(
    artifact: Dict[str, Any],
    *,
    claims_key: str,
    sources_key: str,
    min_citations_per_claim: int,
) -> Tuple[float, float, List[Dict[str, Any]]]:
    """
    Returns:
      - E_claim_coverage: fraction of claims with >= min citations
      - E_source_resolve_rate: fraction of all cited ids that exist in sources
      - claim_rows: details for csv/json
    """
    claims = _as_list(artifact.get(claims_key))
    sources = _as_list(artifact.get(sources_key))

    source_ids = {str(s.get("id")) for s in sources if isinstance(s, dict) and _nonempty_str(s.get("id"))}

    good_claims = 0
    total_claims = 0
    cited_total = 0
    cited_resolved = 0

    claim_rows: List[Dict[str, Any]] = []

    for c in claims:
        if not isinstance(c, dict):
            continue
        total_claims += 1
        cid = str(c.get("id", f"c{total_claims}"))
        text = str(c.get("text", ""))
        cits = _as_list(c.get("citations"))
        cits = [str(x) for x in cits if _nonempty_str(str(x))]

        ok_c = len(cits) >= int(min_citations_per_claim)
        if ok_c:
            good_claims += 1

        missing_cits = [x for x in cits if x not in source_ids]
        cited_total += len(cits)
        cited_resolved += len([x for x in cits if x in source_ids])

        claim_rows.append(
            {
                "claim_id": cid,
                "claim_text": text,
                "citations": ";".join(cits),
                "citations_count": len(cits),
                "citations_min_required": int(min_citations_per_claim),
                "citations_ok": bool(ok_c),
                "missing_citations": ";".join(missing_cits),
                "missing_citations_count": len(missing_cits),
            }
        )

    E_claim = (good_claims / total_claims) if total_claims > 0 else 0.0
    E_resolve = (cited_resolved / cited_total) if cited_total > 0 else 0.0
    return float(E_claim), float(E_resolve), claim_rows


def _evidence_links_ok(artifact: Dict[str, Any], evidence_key: str, min_links: int) -> Tuple[int, int, bool]:
    ev = _as_dict(artifact.get(evidence_key))
    links = _as_list(ev.get("links"))
    links = [str(x).strip() for x in links if _nonempty_str(x)]
    return int(len(links)), int(min_links), bool(len(links) >= int(min_links))


def _ethical_symmetry_proxy_ok(artifact: Dict[str, Any]) -> bool:
    """
    Proxy for E_s: ensure disclosure + reporting channel + escalation exist.
    """
    sec = _as_dict(artifact.get("sections"))
    disclosure_ok = _nonempty_str(sec.get("disclosure")) or _nonempty_str(artifact.get("disclosure"))
    rc = _as_dict(artifact.get("reporting_channel"))
    channel_ok = _nonempty_str(rc.get("primary")) and _nonempty_str(rc.get("escalation"))
    return bool(disclosure_ok and channel_ok)


def _compute_drift_token_jaccard(base_answer: str, perturbations: List[Dict[str, Any]]) -> Tuple[Optional[float], Optional[float], int]:
    if not _nonempty_str(base_answer):
        return None, None, 0
    base_t = tokenize(base_answer)
    ds: List[float] = []

    for p in perturbations:
        if not isinstance(p, dict):
            continue
        ans = p.get("answer")
        if not _nonempty_str(ans):
            continue
        ds.append(float(jaccard_distance(base_t, tokenize(str(ans)))))

    if not ds:
        return None, None, 0
    return float(mean(ds)), float(max(ds)), int(len(ds))


def _compute_lambda_flip_rate(perturbations: List[Dict[str, Any]], decision_key: str) -> Tuple[Optional[float], Optional[str], int]:
    labels: List[str] = []
    for p in perturbations:
        if not isinstance(p, dict):
            continue
        lab = p.get(decision_key)
        if _nonempty_str(lab):
            labels.append(str(lab).strip())

    if len(labels) < 2:
        return None, None, int(len(labels))

    mode = _mode_label(labels)
    if mode is None:
        return None, None, int(len(labels))

    flips = sum(1 for x in labels if x != mode)
    return float(flips / len(labels)), mode, int(len(labels))


def _write_json(path: Path, obj: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")


def _write_claims_csv(path: Path, claim_rows: List[Dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fields = [
        "claim_id",
        "claim_text",
        "citations",
        "citations_count",
        "citations_min_required",
        "citations_ok",
        "missing_citations",
        "missing_citations_count",
    ]
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for r in claim_rows:
            w.writerow({k: r.get(k, "") for k in fields})


def _write_markdown(
    path: Path,
    *,
    metrics: Dict[str, Any],
    flags: Dict[str, Any],
    required_sections: List[str],
    present_sections: List[str],
    missing_sections: List[str],
    claim_rows: List[Dict[str, Any]],
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)

    def fmt(x: Any) -> str:
        if x is None:
            return "n/a"
        if isinstance(x, float):
            return f"{x:.4f}"
        return str(x)

    lines: List[str] = []
    lines.append("# Coherence Audit")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append("| metric | value |")
    lines.append("|---|---:|")
    for k in [
        "E_claim_coverage",
        "E_source_resolve_rate",
        "T_required_sections_coverage",
        "Psi",
        "DeltaS_mean",
        "DeltaS_max",
        "Lambda_flip_rate",
        "Es_fields_ok",
    ]:
        if k in metrics:
            lines.append(f"| {k} | {fmt(metrics.get(k))} |")
    lines.append("")
    lines.append("## Flags")
    lines.append("")
    for k, v in flags.items():
        lines.append(f"- **{k}**: {v}")
    lines.append("")
    lines.append("## Traceability sections")
    lines.append("")
    lines.append(f"- required: {required_sections}")
    lines.append(f"- present: {present_sections}")
    lines.append(f"- missing: {missing_sections}")
    lines.append("")
    lines.append("## Claims (preview)")
    lines.append("")
    lines.append("| claim_id | citations_ok | citations_count | missing_citations_count |")
    lines.append("|---|---:|---:|---:|")
    for r in claim_rows[:25]:
        lines.append(
            f"| {r.get('claim_id','')} | {r.get('citations_ok')} | {r.get('citations_count')} | {r.get('missing_citations_count')} |"
        )
    if len(claim_rows) > 25:
        lines.append("")
        lines.append(f"_({len(claim_rows)-25} more claims omitted; see CSV.)_")
    lines.append("")

    path.write_text("\n".join(lines), encoding="utf-8")


def coherence_audit_task(
    task_doc: Dict[str, Any],
    outdir: Path,
    thresholds: Dict[str, Any],
    *,
    sections_key: str,
    claims_key: str = "claims",
    sources_key: str = "sources",
    evidence_key: str = "evidence",
    perturbations_key: str = "perturbations",
    decision_key: str = "decision_label",
    required_sections: Optional[List[str]] = None,
    min_citations_per_claim: int = 1,
    min_evidence_links: int = 1,
    compute_drift: bool = True,
    compute_lambda: bool = True,
    drift_method: str = "token_jaccard",
    write_audit_json: bool = True,
    write_audit_md: bool = True,
    write_claims_csv: bool = True,
    name_audit_json: str = "coherence_audit.json",
    name_audit_md: str = "coherence_audit.md",
    name_claims_csv: str = "coherence_claims.csv",
) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    """
    UCC step entry point: returns metrics, flags, output_paths
    """
    outdir.mkdir(parents=True, exist_ok=True)

    required_sections = required_sections or ["assumptions", "limitations", "uncertainty", "disclosure"]

    artifact = task_doc.get(sections_key)
    if not isinstance(artifact, dict):
        raise ValueError(f"coherence_audit expects a dict at task_doc['{sections_key}'].")

    # Threshold defaults
    evidence_min = _get_threshold(thresholds, "evidence_min", 0.8)
    traceability_min = _get_threshold(thresholds, "traceability_min", 0.6)
    psi_min = _get_threshold(thresholds, "psi_min", 0.6)
    deltaS_max_thr = _get_threshold(thresholds, "deltaS_max", 0.35)
    lambda_flip_max = _get_threshold(thresholds, "lambda_flip_max", 0.2)

    metrics: Dict[str, Any] = {}
    flags: Dict[str, Any] = {}
    outputs: List[Path] = []

    # T: required sections coverage
    req, present, missing, T_cov = _required_sections_coverage(artifact, required_sections)
    metrics["required_sections"] = req
    metrics["present_sections"] = present
    metrics["missing_sections"] = missing
    metrics["T_required_sections_coverage"] = float(T_cov)

    # E: claim coverage + source resolve rate
    E_claim, E_resolve, claim_rows = _claim_metrics(
        artifact,
        claims_key=claims_key,
        sources_key=sources_key,
        min_citations_per_claim=int(min_citations_per_claim),
    )
    metrics["E_claim_coverage"] = float(E_claim)
    metrics["E_source_resolve_rate"] = float(E_resolve)

    # Evidence links
    links_count, links_min, links_ok = _evidence_links_ok(artifact, evidence_key, int(min_evidence_links))
    metrics["evidence_links_count"] = int(links_count)
    metrics["evidence_links_min_required"] = int(links_min)
    flags["evidence_links_ok"] = bool(links_ok)

    # Ψ
    Psi = float(E_claim * T_cov)
    metrics["Psi"] = Psi

    # E_s proxy
    Es_ok = _ethical_symmetry_proxy_ok(artifact)
    metrics["Es_fields_ok"] = 1 if Es_ok else 0

    # ΔS
    perturbations = _as_list(artifact.get(perturbations_key))
    delta_mean = delta_max = None
    if compute_drift:
        if drift_method != "token_jaccard":
            raise ValueError(f"Unsupported drift_method '{drift_method}'.")
        base_answer = str(artifact.get("answer", "") or "")
        delta_mean, delta_max, n_used = _compute_drift_token_jaccard(base_answer, perturbations)
        metrics["DeltaS_n"] = int(n_used)
        metrics["DeltaS_mean"] = float(delta_mean) if delta_mean is not None else None
        metrics["DeltaS_max"] = float(delta_max) if delta_max is not None else None
        flags["deltaS_skipped"] = bool(delta_mean is None)
    else:
        flags["deltaS_skipped"] = True
        metrics["DeltaS_mean"] = None
        metrics["DeltaS_max"] = None

    # Λ
    flip_rate = None
    mode_label = None
    if compute_lambda:
        flip_rate, mode_label, n_used = _compute_lambda_flip_rate(perturbations, decision_key=decision_key)
        metrics["Lambda_n"] = int(n_used)
        metrics["Lambda_mode_label"] = mode_label
        metrics["Lambda_flip_rate"] = float(flip_rate) if flip_rate is not None else None
        flags["lambda_skipped"] = bool(flip_rate is None)
    else:
        flags["lambda_skipped"] = True
        metrics["Lambda_flip_rate"] = None

    # Flags vs thresholds
    flags["pass_evidence"] = bool(
        links_ok and (E_claim >= evidence_min) and (E_resolve >= evidence_min)
    )
    flags["pass_traceability"] = bool(T_cov >= traceability_min)
    flags["pass_psi"] = bool(Psi >= psi_min)

    flags["pass_deltaS"] = True if flags.get("deltaS_skipped", False) else bool((delta_max is not None) and (delta_max <= deltaS_max_thr))
    flags["pass_lambda"] = True if flags.get("lambda_skipped", False) else bool((flip_rate is not None) and (flip_rate <= lambda_flip_max))
    flags["pass_Es"] = bool(Es_ok)

    flags["overall_pass"] = bool(
        flags["pass_evidence"]
        and flags["pass_traceability"]
        and flags["pass_psi"]
        and flags["pass_deltaS"]
        and flags["pass_lambda"]
        and flags["pass_Es"]
    )

    # Write artifacts
    if write_claims_csv:
        p = outdir / name_claims_csv
        _write_claims_csv(p, claim_rows)
        outputs.append(p)

    if write_audit_json:
        p = outdir / name_audit_json
        _write_json(
            p,
            {
                "schema_version": "0.1",
                "task": "coherence_audit",
                "sections_key": sections_key,
                "metrics": metrics,
                "flags": flags,
                "claim_rows_preview": claim_rows[:10],
            },
        )
        outputs.append(p)

    if write_audit_md:
        p = outdir / name_audit_md
        _write_markdown(
            p,
            metrics=metrics,
            flags=flags,
            required_sections=req,
            present_sections=present,
            missing_sections=missing,
            claim_rows=claim_rows,
        )
        outputs.append(p)

    return metrics, flags, outputs


# Convenience alias (so either name works)
coherence_audit = coherence_audit_task

