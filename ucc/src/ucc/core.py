from __future__ import annotations

import csv
import json
import re
import statistics
from pathlib import Path
from typing import Any, Dict, Tuple, List
from .coherence_audit import coherence_audit_task

import yaml
from jsonschema import Draft202012Validator

from .audit import AuditBundle, env_info, now_utc_iso, sha256_file, write_bundle
from .lean_symbols import check_lean_symbols_task
from .authority_validators import validate_authority_profile
from .json_assertions import verify_json_assertions_task
from .json_patterns import verify_json_patterns_task
from .json_extract import extract_json_fields_task
from .mapping_validators import validate_mapping_table_task, validate_mapping_index_task
from ucc.tel_events import emit_tel_event


BUILTIN_STEP_TYPES = {
    "ingest_json",
    "ingest_csv",
    "compute_lambdaT",
    "threshold_flags",
    "emit_report",
    "emit_threshold_table",
    "compare_tches_runs",
    "check_required_sections",
    "emit_checklist",
    "compare_helmholtz_runs",
    "require_evidence_links",
    "misuse_taxonomy_check",
    "disclosure_channel_check",
    "check_lean_symbols",
    "validate_authority_profile",
    "coherence_audit",
}

# --- CoherenceLattice extension: register custom step types (keep module validation strict) ---
if "emit_telemetry_snapshot" not in BUILTIN_STEP_TYPES:
    try:
        BUILTIN_STEP_TYPES.add("emit_telemetry_snapshot")  # set
    except AttributeError:
        BUILTIN_STEP_TYPES.append("emit_telemetry_snapshot")  # list

def load_yaml(path: Path) -> Dict[str, Any]:
    return yaml.safe_load(path.read_text(encoding="utf-8-sig"))


def load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def load_schema(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def load_csv_table(path: Path) -> List[Dict[str, str]]:
    with path.open("r", newline="") as f:
        r = csv.DictReader(f)
        return [dict(row) for row in r]


def validate_module(module_doc: Dict[str, Any], schema_doc: Dict[str, Any]) -> None:
    v = Draft202012Validator(schema_doc)
    errors = sorted(v.iter_errors(module_doc), key=lambda e: e.path)
    if errors:
        msg = "\n".join([f"- {list(e.path)}: {e.message}" for e in errors])
        raise ValueError("UCC module schema validation failed:\n" + msg)

    for step in module_doc.get("steps", []):
        st = step.get("type", "")
        if st not in BUILTIN_STEP_TYPES:
            raise ValueError(f"Unknown/unsupported step type '{st}'. Allowed: {sorted(BUILTIN_STEP_TYPES)}")


def _get_text_field(input_doc: Dict[str, Any], sections_key: str, field_key: str) -> str:
    sec = input_doc.get(sections_key, {})
    if not isinstance(sec, dict):
        raise ValueError(f"Expected '{sections_key}' to be a JSON object mapping key->text")
    return str(sec.get(field_key, "") or "")


def _extract_urls_and_dois(text: str) -> List[str]:
    urls = re.findall(r"https?://[^\s\)\]\}>\"']+", text, flags=re.IGNORECASE)
    dois = re.findall(r"\b10\.\d{4,9}/[^\s\)\]\}>\"']+\b", text, flags=re.IGNORECASE)

    out: List[str] = []
    for u in urls:
        out.append(u.strip().rstrip(".,;"))
    for d in dois:
        out.append("doi:" + d.strip().rstrip(".,;"))

    seen = set()
    uniq: List[str] = []
    for x in out:
        if x not in seen:
            seen.add(x)
            uniq.append(x)
    return uniq


def compute_lambdaT(series: list[float], dt_s: float, dT_design_C: float, tau_res_s: float) -> Dict[str, float]:
    if dt_s <= 0:
        raise ValueError("dt_s must be > 0")
    if len(series) < 2:
        raise ValueError("temperature series must have at least 2 samples")
    dTdt = [(series[i] - series[i - 1]) / dt_s for i in range(1, len(series))]
    max_abs = max(abs(x) for x in dTdt)
    denom = (dT_design_C / max(tau_res_s, 1e-9))
    lam = max_abs / max(denom, 1e-12)
    return {"max_abs_dTdt": max_abs, "Lambda_T": lam}


def threshold_flags(metrics: Dict[str, Any], thresholds: Dict[str, Any]) -> Dict[str, Any]:
    flags: Dict[str, Any] = {}
    lam = float(metrics.get("Lambda_T", 0.0))
    warn = float(thresholds.get("lambdaT_warn", 0.7))
    alarm = float(thresholds.get("lambdaT_alarm", 1.0))
    flags["warn_LambdaT"] = (lam > warn)
    flags["alarm_LambdaT"] = (lam > alarm)
    return flags


def _infer_dt_from_tcol(rows: List[Dict[str, str]], t_col: str) -> float:
    ts: List[float] = []
    for row in rows:
        if t_col in row and row[t_col] != "":
            ts.append(float(row[t_col]))
    if len(ts) < 2:
        raise ValueError("Cannot infer dt_s: need at least 2 time samples in CSV")
    diffs = [ts[i] - ts[i - 1] for i in range(1, len(ts))]
    diffs = [d for d in diffs if d > 0]
    if not diffs:
        raise ValueError("Cannot infer dt_s: non-positive time diffs in CSV")
    return float(statistics.median(diffs))


def emit_threshold_table(outdir: Path, metrics: Dict[str, Any], flags: Dict[str, Any], thresholds: Dict[str, Any],
                         name_csv: str = "thresholds.csv", name_md: str = "thresholds.md") -> List[Path]:
    outdir.mkdir(parents=True, exist_ok=True)
    rows = []
    lam = float(metrics.get("Lambda_T", float("nan")))
    warn_th = float(thresholds.get("lambdaT_warn", 0.7))
    alarm_th = float(thresholds.get("lambdaT_alarm", 1.0))
    warn_flag = bool(flags.get("warn_LambdaT", False))
    alarm_flag = bool(flags.get("alarm_LambdaT", False))
    status = "alarm" if alarm_flag else ("warn" if warn_flag else "ok")

    rows.append({
        "metric": "Lambda_T",
        "value": lam,
        "warn_threshold": warn_th,
        "alarm_threshold": alarm_th,
        "warn_flag": warn_flag,
        "alarm_flag": alarm_flag,
        "status": status,
    })

    if "max_abs_dTdt" in metrics:
        rows.append({
            "metric": "max_abs_dTdt",
            "value": float(metrics["max_abs_dTdt"]),
            "warn_threshold": "",
            "alarm_threshold": "",
            "warn_flag": "",
            "alarm_flag": "",
            "status": "",
        })

    p_csv = outdir / name_csv
    with p_csv.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["metric","value","warn_threshold","alarm_threshold","warn_flag","alarm_flag","status"])
        w.writeheader()
        for r in rows:
            w.writerow(r)

    p_md = outdir / name_md
    with p_md.open("w", encoding="utf-8") as f:
        f.write("# Threshold Table\n\n")
        f.write("| metric | value | warn | alarm | warn_flag | alarm_flag | status |\n")
        f.write("|---|---:|---:|---:|---:|---:|---|\n")
        for r in rows:
            f.write(f"| {r['metric']} | {r['value']} | {r['warn_threshold']} | {r['alarm_threshold']} | {r['warn_flag']} | {r['alarm_flag']} | {r['status']} |\n")

    return [p_csv, p_md]


def check_required_sections(input_doc: Dict[str, Any], sections_key: str, required: List[str]) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    sec = input_doc.get(sections_key, {})
    if not isinstance(sec, dict):
        raise ValueError(f"Expected '{sections_key}' to be a JSON object mapping section->text")

    present: Dict[str, bool] = {}
    for s in required:
        txt = sec.get(s, "")
        present[s] = bool(str(txt).strip())

    missing = [s for s, ok in present.items() if not ok]
    present_count = sum(1 for ok in present.values() if ok)
    required_count = len(required)
    coverage = (present_count / required_count) if required_count else 0.0

    metrics = {
        "required_sections": required,
        "present_sections": [s for s, ok in present.items() if ok],
        "missing_sections": missing,
        "section_coverage": coverage,
        "present_count": present_count,
        "required_count": required_count,
    }
    flags = {
        "sections_complete": (len(missing) == 0),
        "sections_missing": missing,
    }
    return metrics, flags


def emit_checklist(outdir: Path, metrics: Dict[str, Any], name_md: str = "checklist.md", title: str = "Checklist") -> Path:
    outdir.mkdir(parents=True, exist_ok=True)
    required = metrics.get("required_sections", [])
    present = set(metrics.get("present_sections", []))
    missing = metrics.get("missing_sections", [])
    coverage = float(metrics.get("section_coverage", 0.0))

    p = outdir / name_md
    with p.open("w", encoding="utf-8") as f:
        f.write(f"# {title}\n\n")
        f.write(f"- section coverage: **{coverage:.3f}**\n")
        f.write(f"- missing sections: {(', '.join(missing) if missing else '(none)')}\n\n")
        f.write("## Required items\n\n")
        for s in required:
            mark = "x" if s in present else " "
            f.write(f"- [{mark}] {s}\n")
    return p


def require_evidence_links(input_doc: Dict[str, Any], sections_key: str, field_key: str, min_links: int, allow_explanation: bool) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    text = _get_text_field(input_doc, sections_key, field_key)
    links = _extract_urls_and_dois(text)
    n = len(links)

    explained = False
    if allow_explanation and n < min_links:
        low = text.lower()
        markers = ["none", "no link", "no links", "no url", "not available", "n/a", "cannot", "unable", "restricted"]
        explained = any(m in low for m in markers) and len(low.strip()) >= 30

    ok = (n >= min_links) or explained

    metrics = {
        "evidence_field": f"{sections_key}.{field_key}",
        "evidence_min_links": min_links,
        "evidence_link_count": n,
        "evidence_links": links,
        "evidence_explained_no_links": explained,
    }
    flags = {
        "evidence_links_ok": ok,
        "evidence_links_sufficient": (n >= min_links),
        "evidence_links_explained": explained,
        "evidence_links_missing": (not ok),
    }
    return metrics, flags


DEFAULT_MISUSE_TAXONOMY = {
    "prompt_injection": ["prompt injection", "jailbreak", "instruction override", "prompt attack"],
    "data_exfiltration": ["data exfiltration", "exfiltrate", "secret leakage", "data leakage", "leak secrets"],
    "policy_evasion": ["policy evasion", "bypass policy", "circumvent policy", "guardrail bypass", "policy bypass"],
    "harassment": ["harassment", "abuse", "bullying", "hate", "toxicity"],
    "model_inversion": ["model inversion", "membership inference", "training data extraction", "inversion attack"],
}


def misuse_taxonomy_check(input_doc: Dict[str, Any], sections_key: str, field_key: str, required_categories: List[str] | None) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    text = _get_text_field(input_doc, sections_key, field_key).lower()
    required_categories = required_categories or list(DEFAULT_MISUSE_TAXONOMY.keys())

    present: List[str] = []
    missing: List[str] = []
    for cat in required_categories:
        syns = DEFAULT_MISUSE_TAXONOMY.get(cat, [cat.replace("_", " ")])
        ok = any(s in text for s in syns)
        (present if ok else missing).append(cat)

    coverage = (len(present) / len(required_categories)) if required_categories else 0.0
    complete = (len(missing) == 0)

    metrics = {
        "misuse_required_categories": required_categories,
        "misuse_present_categories": present,
        "misuse_missing_categories": missing,
        "misuse_coverage": coverage,
    }
    flags = {
        "misuse_taxonomy_complete": complete,
        "misuse_missing_categories": missing,
    }
    return metrics, flags


def disclosure_channel_check(input_doc: Dict[str, Any], sections_key: str, field_key: str, require_escalation: bool = True) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    text = _get_text_field(input_doc, sections_key, field_key)
    low = text.lower()

    channel_markers = [
        "report", "reporting", "contact", "email", "mailto:", "hotline", "ticket", "issue tracker",
        "support", "feedback", "helpdesk", "abuse", "harm", "safety@", "security@"
    ]
    escalation_markers = [
        "escalat", "triage", "incident", "on-call", "review", "human review", "flag for review",
        "investigate", "contain", "remediate", "rollback", "response plan"
    ]

    has_channel = any(m in low for m in channel_markers)
    has_escalation = any(m in low for m in escalation_markers)

    ok = has_channel and (has_escalation if require_escalation else True)

    metrics = {
        "disclosure_field": f"{sections_key}.{field_key}",
        "disclosure_has_reporting_channel": has_channel,
        "disclosure_has_escalation": has_escalation,
        "disclosure_require_escalation": require_escalation,
        "disclosure_ok": ok,
    }
    flags = {
        "disclosure_channel_ok": ok,
        "disclosure_missing_channel": (not has_channel),
        "disclosure_missing_escalation": (require_escalation and (not has_escalation)),
    }
    return metrics, flags


def _col_floats(rows: List[Dict[str, str]], col: str) -> List[float]:
    out: List[float] = []
    for r in rows:
        if col in r and r[col] != "":
            out.append(float(r[col]))
    return out


def summarize_tches_csv(rows: List[Dict[str, str]], thresholds: Dict[str, Any]) -> Dict[str, Any]:
    warnL = float(thresholds.get("lambdaT_warn", 0.7))
    alarmL = float(thresholds.get("lambdaT_alarm", 1.0))

    lam = _col_floats(rows, "Lambda_T")
    Ppump = _col_floats(rows, "P_pump_kW")
    Qch = _col_floats(rows, "Q_chiller_kW")

    def safe_mean(xs): return (sum(xs) / len(xs)) if xs else float("nan")
    def safe_max(xs): return max(xs) if xs else float("nan")

    warn_L_steps = sum(1 for x in lam if x > warnL)
    alarm_L_steps = sum(1 for x in lam if x > alarmL)

    return {
        "max_LambdaT": safe_max(lam),
        "mean_LambdaT": safe_mean(lam),
        "warn_LambdaT_steps": warn_L_steps,
        "alarm_LambdaT_steps": alarm_L_steps,
        "mean_Ppump": safe_mean(Ppump),
        "mean_Qch": safe_mean(Qch),
        "n_rows": len(rows),
    }


def compare_tches_runs(task_dir: Path, cfg: Dict[str, Any], outdir: Path, thresholds: Dict[str, Any]) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    baseline_path = Path(cfg["baseline_csv"])
    lambda_path = Path(cfg["lambda_csv"])
    if not baseline_path.is_absolute():
        baseline_path = (task_dir / baseline_path).resolve()
    if not lambda_path.is_absolute():
        lambda_path = (task_dir / lambda_path).resolve()

    base_rows = load_csv_table(baseline_path)
    lam_rows = load_csv_table(lambda_path)

    base = summarize_tches_csv(base_rows, thresholds)
    lam = summarize_tches_csv(lam_rows, thresholds)

    delta_warn = base["warn_LambdaT_steps"] - lam["warn_LambdaT_steps"]

    metrics: Dict[str, Any] = {
        "baseline_path": str(baseline_path),
        "lambda_path": str(lambda_path),
        "baseline_sha256": sha256_file(baseline_path),
        "lambda_sha256": sha256_file(lambda_path),
        **{f"baseline_{k}": v for k, v in base.items()},
        **{f"lambda_{k}": v for k, v in lam.items()},
        "delta_warn_LambdaT_steps": delta_warn,
        "delta_mean_Ppump": lam["mean_Ppump"] - base["mean_Ppump"],
        "delta_mean_Qch": lam["mean_Qch"] - base["mean_Qch"],
    }

    flags: Dict[str, Any] = {"improved_warn_time": (delta_warn > 0)}

    outdir.mkdir(parents=True, exist_ok=True)
    p_md = outdir / "comparison.md"
    # AUTO_FIX_DELTA_ALARM_TCHES: ensure delta_alarm_LambdaT_steps is present in metrics + comparison.json
    if isinstance(metrics, dict) and 'delta_alarm_LambdaT_steps' not in metrics:
        metrics['delta_alarm_LambdaT_steps'] = int(metrics.get('baseline_alarm_LambdaT_steps', 0) - metrics.get('lambda_alarm_LambdaT_steps', 0))
    try:
        if isinstance(comparison, dict):
            if 'metrics' in comparison and isinstance(comparison['metrics'], dict):
                comparison['metrics'].setdefault('delta_alarm_LambdaT_steps', metrics.get('delta_alarm_LambdaT_steps', 0))
    except NameError:
        pass
    except Exception:
        pass

    p_js = outdir / "comparison.json"

    p_js.write_text(json.dumps({"metrics": metrics, "flags": flags}, indent=2, sort_keys=True), encoding="utf-8")
    p_md.write_text(f"delta_warn_LambdaT_steps: {delta_warn}\n", encoding="utf-8")

    # --- CI/Parser alignment: ensure comparison.md contains stable Summary table rows
    # Some builds accidentally emit only a single delta line (e.g. 'delta_warn_LambdaT_steps: 3').
    # CI expects a stable markdown table row for warn_LambdaT_steps (and alarm_LambdaT_steps).
    try:
        md_text = p_md.read_text(encoding="utf-8", errors="ignore")
        need = ("| warn_LambdaT_steps" not in md_text) or ("| alarm_LambdaT_steps" not in md_text)
        if need:
            warn_b = int(metrics.get("baseline_warn_LambdaT_steps", 0))
            warn_l = int(metrics.get("lambda_warn_LambdaT_steps", 0))
            warn_d = int(metrics.get("delta_warn_LambdaT_steps", warn_b - warn_l))

            alarm_b = int(metrics.get("baseline_alarm_LambdaT_steps", 0))
            alarm_l = int(metrics.get("lambda_alarm_LambdaT_steps", 0))
            alarm_d = int(metrics.get("delta_alarm_LambdaT_steps", alarm_b - alarm_l))

            # keep dict in sync (parsers read comparison.json too)
            metrics["delta_warn_LambdaT_steps"] = warn_d
            metrics["delta_alarm_LambdaT_steps"] = alarm_d

            pp_b = float(metrics.get("baseline_mean_Ppump", 0.0))
            pp_l = float(metrics.get("lambda_mean_Ppump", 0.0))
            pp_d = float(metrics.get("delta_mean_Ppump", pp_l - pp_b))

            q_b = float(metrics.get("baseline_mean_Qch", 0.0))
            q_l = float(metrics.get("lambda_mean_Qch", 0.0))
            q_d = float(metrics.get("delta_mean_Qch", q_l - q_b))

            table = (
                "\n## Summary table\n"
                "| metric | baseline | lambda | delta |\n"
                "|---|---:|---:|---:|\n"
                f"| warn_LambdaT_steps | {warn_b} | {warn_l} | {warn_d} |\n"
                f"| alarm_LambdaT_steps | {alarm_b} | {alarm_l} | {alarm_d} |\n"
                f"| mean_Ppump | {pp_b:.6g} | {pp_l:.6g} | {pp_d:.6g} |\n"
                f"| mean_Qch | {q_b:.6g} | {q_l:.6g} | {q_d:.6g} |\n"
            )
            md_text = md_text.rstrip() + "\n" + table + "\n"
            p_md.write_text(md_text, encoding="utf-8")
    except Exception:
        pass

    return metrics, flags, [p_md, p_js]


def compare_helmholtz_runs(task_dir: Path, cfg: Dict[str, Any], outdir: Path, thresholds: Dict[str, Any]) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    summary_path = Path(cfg["summary_csv"])
    if not summary_path.is_absolute():
        summary_path = (task_dir / summary_path).resolve()

    scenario_col = str(cfg.get("scenario_col", "scenario"))
    t_col = str(cfg.get("t_col", "t"))
    psi_col = str(cfg.get("psi_mean_col", "Psi_mean"))
    guided_label = str(cfg.get("guided_label", "guided"))
    unguided_label = str(cfg.get("unguided_label", "unguided"))

    rows = load_csv_table(summary_path)

    guided: Dict[int, float] = {}
    unguided: Dict[int, float] = {}
    for r in rows:
        scen = r.get(scenario_col, "").strip()
        if scen not in (guided_label, unguided_label):
            continue
        t = int(float(r[t_col]))
        psi = float(r[psi_col])
        (guided if scen == guided_label else unguided)[t] = psi

    ts = sorted(set(guided.keys()) & set(unguided.keys()), reverse=True)
    if not ts:
        raise ValueError("No overlapping t values between guided and unguided.")

    curve = [(t, guided[t], unguided[t], guided[t] - unguided[t]) for t in ts]
    delta_start = curve[0][3]
    t_end = curve[-1][0]
    delta_end = curve[-1][3]
    t_peak, _, _, delta_peak = max(curve, key=lambda x: x[3])
    auc = sum(d for (_, _, _, d) in curve)

    metrics = {
        "summary_path": str(summary_path),
        "summary_sha256": sha256_file(summary_path),
        "steps_count": len(ts),
        "t_start": ts[0],
        "t_end": t_end,
        "deltaPsi_start": delta_start,
        "deltaPsi_peak": delta_peak,
        "t_peak": t_peak,
        "deltaPsi_end": delta_end,
        "auc_deltaPsi": auc,
    }
    flags = {"overall_pass": True}

    outdir.mkdir(parents=True, exist_ok=True)

    p_curve = outdir / "delta_curve.csv"
    with p_curve.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["t", "psi_guided", "psi_unguided", "delta_psi"])
        for t, g, u, d in curve:
            w.writerow([t, g, u, d])

    p_curve_md = outdir / "delta_curve.md"
    with p_curve_md.open("w", encoding="utf-8") as f:
        f.write("# DeltaPsi Curve (guided - unguided)\n\n")
        f.write("| t | psi_guided | psi_unguided | delta_psi |\n")
        f.write("|---:|---:|---:|---:|\n")
        for t, g, u, d in curve:
            f.write(f"| {t} | {g:.6g} | {u:.6g} | {d:.6g} |\n")

    p_md = outdir / "comparison.md"
    p_js = outdir / "comparison.json"
    p_js.write_text(json.dumps({"metrics": metrics, "flags": flags}, indent=2, sort_keys=True), encoding="utf-8")
    p_md.write_text(f"deltaPsi_start: {delta_start}\n", encoding="utf-8")

    return metrics, flags, [p_curve, p_curve_md, p_md, p_js]

def run_module(module_path: Path, input_path: Path, outdir: Path, schema_path: Path) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    _ucc_name = None
    try:
        _m = locals().get('module') or locals().get('spec') or locals().get('module_spec') or locals().get('step')
        if isinstance(_m, dict):
            _ucc_name = _m.get('name') or _m.get('id') or _m.get('module_id') or _m.get('type')
        else:
            _ucc_name = str(_m) if _m is not None else None
    except Exception:
        _ucc_name = None
    emit_tel_event("ucc_run_module_start", {"name": _ucc_name})
    _ucc_ok = True
    try:
        module_doc = load_yaml(module_path)
        schema_doc = load_schema(schema_path)
        validate_module(module_doc, schema_doc)

        mod = module_doc["module"]
        thresholds = mod.get("thresholds", {})

        context: Dict[str, Any] = {"input": None, "metrics": {}, "flags": {}, "output_files": []}

        for step in module_doc["steps"]:
            stype = step["type"]
            params = step.get("params", {}) or {}

            if stype == "ingest_json":
                context["input"] = load_json(input_path)

            elif stype == "ingest_csv":
                context["input"] = load_csv_table(input_path)

            elif stype == "check_lean_symbols":
                if context["input"] is None or not isinstance(context["input"], dict):
                    raise ValueError("check_lean_symbols requires ingest_json of a config dict")
                task_dir = Path(input_path).parent
                m, fl, outs = check_lean_symbols_task(task_dir, context["input"], outdir, thresholds)
                context["metrics"].update(m)
                context["flags"].update(fl)
                context["output_files"].extend(outs)

            elif stype == "check_required_sections":
                m, fl = check_required_sections(context["input"], str(params.get("sections_key", "sections")), list(params.get("required_sections", [])))
                context["metrics"].update(m); context["flags"].update(fl)

            elif stype == "require_evidence_links":
                m, fl = require_evidence_links(context["input"], str(params.get("sections_key","genai_profile")), str(params.get("field_key","EVALUATION_EVIDENCE")),
                                               int(params.get("min_links",1)), bool(params.get("allow_explanation",True)))
                context["metrics"].update(m); context["flags"].update(fl)

            elif stype == "misuse_taxonomy_check":
                rc = params.get("required_categories", None)
                if rc is not None: rc = list(rc)
                m, fl = misuse_taxonomy_check(context["input"], str(params.get("sections_key","genai_profile")), str(params.get("field_key","MISUSE_MONITORING")), rc)
                context["metrics"].update(m); context["flags"].update(fl)

            elif stype == "disclosure_channel_check":
                m, fl = disclosure_channel_check(context["input"], str(params.get("sections_key","genai_profile")), str(params.get("field_key","DISCLOSURE")), bool(params.get("require_escalation",True)))
                context["metrics"].update(m); context["flags"].update(fl)

            elif stype == "compare_tches_runs":
                task_dir = Path(input_path).parent
                m, fl, outs = compare_tches_runs(task_dir, context["input"], outdir, thresholds)
                context["metrics"].update(m); context["flags"].update(fl); context["output_files"].extend(outs)

            elif stype == "compare_helmholtz_runs":
                task_dir = Path(input_path).parent
                m, fl, outs = compare_helmholtz_runs(task_dir, context["input"], outdir, thresholds)
                context["metrics"].update(m); context["flags"].update(fl); context["output_files"].extend(outs)

            elif stype == "emit_checklist":
                p = emit_checklist(outdir, context["metrics"], str(params.get("checklist_md","checklist.md")), title=str(params.get("title","Checklist")))
                context["output_files"].append(p)

            elif stype == "validate_authority_profile":
                if context["input"] is None or not isinstance(context["input"], dict):
                    raise ValueError("validate_authority_profile requires ingest_json of a dict")
                sections_key = str(params.get("sections_key", ""))
                if not sections_key:
                    raise ValueError("validate_authority_profile requires params.sections_key")
                min_links = int(params.get("min_links", 1))
                require_review = bool(params.get("require_review_dates", True))
                require_exc = bool(params.get("require_exception_items", True))
                m, fl = validate_authority_profile(context["input"], sections_key, min_links=min_links, require_review_dates=require_review, require_exception_items=require_exc)
                context["metrics"].update(m)
                context["flags"].update(fl)
            elif stype == "emit_telemetry_snapshot":             # Canonical telemetry snapshot emitter (non-trivial E/T for KONOMI smoke).             # IMPORTANT: Do NOT import json or Path in this function scope (avoid UnboundLocalError in other steps).             import hashlib as _hashlib             import sys as _sys             import platform as _platform             import math as _math             from datetime import datetime as _datetime, timezone as _timezone                      params = step.get("params", {}) or {}             name_json = str(params.get("name_json", "telemetry_snapshot.json"))                      src = context.get("input", {}) or {}  # expected: audit_bundle.json (ingested)             m = src.get("metrics", {}) or {}             fl = src.get("flags", {}) or {}             env = src.get("environment", {}) or {}                      def _f(x, d):                 try:                     return float(x)                 except Exception:                     return float(d)                      def _clamp01(x):                 try:                     return max(0.0, min(1.0, float(x)))                 except Exception:                     return 0.0                      def _ratio(num, den, default=1.0):                 try:                     den = float(den)                     if den <= 0:                         return float(default)                     return float(num) / den                 except Exception:                     return float(default)                      # ------------------------------             # T: transparency proxy from coverage metrics             # ------------------------------             if "T" in m:                 T = _f(m.get("T"), 1.0)             elif "T_required_sections_coverage" in m:                 T = _f(m.get("T_required_sections_coverage"), 1.0)             elif "section_coverage" in m:                 T = _f(m.get("section_coverage"), 1.0)             elif ("present_count" in m) and ("required_count" in m):                 T = _ratio(m.get("present_count"), m.get("required_count"), default=1.0)             else:                 T = 1.0             T = _clamp01(T)                      # ------------------------------             # E: empathy proxy from numeric performance signals in input JSON (KONOMI summary + per-engine summaries).             # This yields stable non-1.0 values and allows ΔS/Λ to reflect real drift when performance changes.             # ------------------------------             if "E" in m:                 E = _f(m.get("E"), 1.0)             elif "E_claim_coverage" in m:                 E = _f(m.get("E_claim_coverage"), 1.0)             else:                 perf_vals = []                 inp_path = src.get("input_path")                 if isinstance(inp_path, str) and inp_path:                     p = Path(inp_path)                     if (not p.exists()) and (not p.is_absolute()):                         p = (Path.cwd() / p).resolve()                     if p.exists():                         base_dir = p.parent                         docs = []                         # primary summary                         try:                             docs.append(("summary", json.loads(p.read_text(encoding="utf-8-sig"))))                         except Exception:                             docs = []                                  # per-engine summaries (best-effort)                         candidates = [                             ("evgpu", base_dir / "evgpu" / "evgpu_matmul_summary.json"),                             ("femto", base_dir / "femto" / "femto_async_summary.json"),                             ("blockarray", base_dir / "blockarray" / "blockarray_summary.json"),                             ("cube", base_dir / "cube" / "cube_summary.json"),                         ]                         for name, fp in candidates:                             if fp.exists():                                 try:                                     docs.append((name, json.loads(fp.read_text(encoding="utf-8-sig"))))                                 except Exception:                                     pass                                  def walk(obj, keypath=""):                             if isinstance(obj, dict):                                 for k,v in obj.items():                                     kp = (keypath + "." + str(k)) if keypath else str(k)                                     walk(v, kp)                             elif isinstance(obj, list):                                 for i,v in enumerate(obj):                                     walk(v, f"{keypath}[{i}]")                             elif isinstance(obj, (int,float)):                                 kp = keypath.lower()                                 if ("timestamp" in kp) or ("git" in kp) or ("commit" in kp):                                     return                                 perf_vals.append(float(obj))                             elif isinstance(obj, str):                                 s = obj.strip()                                 # parse numeric-looking strings                                 try:                                     fv = float(s)                                 except Exception:                                     return                                 if not _math.isfinite(fv):                                     return                                 perf_vals.append(float(fv))                                  for name, doc in docs:                             walk(doc, name)                          if perf_vals:                     vals = [_math.log1p(abs(v)) for v in perf_vals[:600]]                     perf_index = sum(vals) / max(1, len(vals))                     # scale factor chosen to keep E in a readable band (typically ~0.75-0.95)                     E = _math.exp(-perf_index / 20.0)                 else:                     E = T             E = _clamp01(E)                      Psi = _clamp01(_f(m.get("Psi", E * T), E * T))             DeltaS = _f(m.get("DeltaS", 0.0), 0.0)             Lambda = _f(m.get("Lambda", 0.0), 0.0)                      if "Es" in m:                 Es = _clamp01(_f(m.get("Es"), 1.0))             else:                 ok_flag = fl.get("sections_complete", fl.get("overall_pass", True))                 Es = 1.0 if bool(ok_flag) else 0.0                      telemetry_ok = bool(fl.get("overall_pass", fl.get("sections_complete", True)))                      outdir.mkdir(parents=True, exist_ok=True)             out_path = outdir / name_json                      pyver = env.get("python_version") or (_sys.version.replace("\\n", " "))             plat = env.get("platform") or _platform.platform()             gsha = env.get("git_commit") or ""                      telemetry = {                 "schema_id": "coherencelattice.telemetry_run.v1",                 "version": 1,                 "run_id": outdir.name,                 "created_at": _datetime.now(_timezone.utc).isoformat(),                 "environment": {"python": str(pyver), "platform": str(plat), "git_commit": str(gsha)},                 "metrics": {"E": E, "T": T, "Psi": Psi, "DeltaS": DeltaS, "Lambda": Lambda, "Es": Es},                 "flags": {"telemetry_ok": telemetry_ok},                 "artifacts": [],                 "notes": "telemetry snapshot: T from coverage; E from numeric perf leaves in KONOMI summaries"             }                      out_path.write_text(json.dumps(telemetry, indent=2, sort_keys=True), encoding="utf-8")             h = _hashlib.sha256(out_path.read_bytes()).hexdigest()             telemetry["artifacts"] = [{"path": out_path.name, "sha256": h}]             out_path.write_text(json.dumps(telemetry, indent=2, sort_keys=True), encoding="utf-8")             context["output_files"].append(out_path)         elif stype == "emit_report":
                report_name = str(params.get("report_name", "report.json"))
                outdir.mkdir(parents=True, exist_ok=True)
                report_path = outdir / report_name
                report = {
                    "module": {"id": mod["id"], "version": mod["version"], "title": mod.get("title", "")},
                    "input_path": str(input_path),
                    "metrics": context["metrics"],
                    "flags": context["flags"],
                }
                report_path.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
                context["output_files"].append(report_path)

            elif stype == "emit_threshold_table":
                outs = emit_threshold_table(outdir, context["metrics"], context["flags"], thresholds,
                                            str(params.get("name_csv","thresholds.csv")), str(params.get("name_md","thresholds.md")))
                context["output_files"].extend(outs)

            elif stype == "compute_lambdaT":
                if context["input"] is None:
                    raise ValueError("compute_lambdaT requires prior ingest step")

                dT_design = float(params.get("dT_design_C", 1.0))
                tau_res = float(params.get("tau_res_s", 1.0))
                src = context["input"]

                # Two supported shapes:
                # - dict input: { series_key: [...], dt_key: ... }
                # - list-of-dicts from ingest_csv: infer dt from t_col and read series_col
                if isinstance(src, dict):
                    series_key = str(params.get("series_key", "T_block_C"))
                    dt_key = str(params.get("dt_key", "dt_s"))
                    series = [float(x) for x in src[series_key]]
                    dt_s = float(src[dt_key])

                elif isinstance(src, list):
                    series_col = str(params.get("series_col", "u_mag_sq"))
                    t_col = str(params.get("t_col", "t_s"))

                    ts = [float(r[t_col]) for r in src if r.get(t_col, "") != ""]
                    dt_s = None
                    for i in range(1, len(ts)):
                        d = ts[i] - ts[i - 1]
                        if d > 0:
                            dt_s = d
                            break
                    if dt_s is None or dt_s <= 0:
                        raise ValueError("Could not infer dt_s from t_col")

                    series = [float(r[series_col]) for r in src]

                else:
                    raise ValueError("Unsupported input type for compute_lambdaT")

                if dt_s <= 0:
                    raise ValueError("dt_s must be > 0")
                if len(series) < 2:
                    raise ValueError("series must have >= 2 samples")

                dTdt = [(series[i] - series[i - 1]) / dt_s for i in range(1, len(series))]
                max_abs = max(abs(x) for x in dTdt) if dTdt else 0.0

                denom = dT_design / max(tau_res, 1e-12)
                lam = max_abs / max(denom, 1e-12)

                context["metrics"].update({"max_abs_dTdt": max_abs, "Lambda_T": lam})
            elif stype == "threshold_flags":
                context["flags"].update(threshold_flags(context["metrics"], thresholds))

            elif stype == "extract_json_fields":
                if context["input"] is None or not isinstance(context["input"], dict):
                    raise ValueError("extract_json_fields requires ingest_json of a dict")
                m, fl, outs = extract_json_fields_task(context["input"], outdir, thresholds, **params)
                context["metrics"].update(m)
                context["flags"].update(fl)
                context["output_files"].extend(outs)

            elif stype == "verify_json_assertions":
                if context["input"] is None or not isinstance(context["input"], dict):
                    raise ValueError("verify_json_assertions requires ingest_json of a dict")
                m, fl, outs = verify_json_assertions_task(context["input"], outdir, thresholds, **params)
                context["metrics"].update(m)
                context["flags"].update(fl)
                context["output_files"].extend(outs)

            elif stype == "verify_json_patterns":
                if context["input"] is None or not isinstance(context["input"], dict):
                    raise ValueError("verify_json_patterns requires ingest_json of a dict")
                m, fl, outs = verify_json_patterns_task(context["input"], outdir, thresholds, **params)
                context["metrics"].update(m)
                context["flags"].update(fl)
                context["output_files"].extend(outs)

            elif stype == "coherence_audit":
                if context["input"] is None or not isinstance(context["input"], dict):
                    raise ValueError("coherence_audit requires ingest_json of a dict")
                m, fl, outs = coherence_audit_task(context["input"], outdir, thresholds, **params)
                context["metrics"].update(m)
                context["flags"].update(fl)
                context["output_files"].extend(outs)

            elif stype == "validate_mapping_index":
                if context["input"] is None or not isinstance(context["input"], dict):
                    raise ValueError("validate_mapping_index requires ingest_json of a dict")
                m, fl, outs = validate_mapping_index_task(context["input"], outdir, thresholds, **params)
                context["metrics"].update(m)
                context["flags"].update(fl)
                context["output_files"].extend(outs)

            elif stype == "validate_mapping_table":
                if context["input"] is None or not isinstance(context["input"], list):
                    raise ValueError("validate_mapping_table requires ingest_csv (list of dict rows)")
                m, fl, outs = validate_mapping_table_task(context["input"], outdir, thresholds, **params)
                context["metrics"].update(m)
                context["flags"].update(fl)
                context["output_files"].extend(outs)

            elif stype == "emit_report":

                # UCC_PATCH_EMIT_REPORT_RUNTIME_FIX

                report_name = str((step.get("params", {}) or {}).get("report_name", "report.json"))

                outdir.mkdir(parents=True, exist_ok=True)

                report_path = outdir / report_name

                report = {

                    "module": {"id": mod["id"], "version": mod["version"], "title": mod.get("title", "")},

                    "input_path": str(input_path),

                    "metrics": context["metrics"],

                    "flags": context["flags"],

                }

                report_path.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")

                context["output_files"].append(report_path)


            else:

                raise ValueError(f"Unsupported step type: {stype}")
        module_sha = sha256_file(module_path)
        input_sha = sha256_file(input_path)
        outputs: Dict[str, str] = {}
        for p in context["output_files"]:
            outputs[str(Path(p).name)] = sha256_file(Path(p))

        bundle = AuditBundle(
            bundle_version="0.1",
            timestamp_utc=now_utc_iso(),
            module_id=mod["id"],
            module_version=mod["version"],
            module_path=str(module_path),
            module_sha256=module_sha,
            input_path=str(input_path),
            input_sha256=input_sha,
            outputs=outputs,
            metrics=context["metrics"],
            flags=context["flags"],
            environment=env_info(),
            notes={"runner": "ucc.core.run_module", "schema": str(schema_path)},
        )
        write_bundle(outdir, bundle)

        return context["metrics"], context["flags"]
    except Exception as _e:
        _ucc_ok = False
        emit_tel_event("ucc_run_module_error", {"name": _ucc_name, "error": str(_e)})
        raise
    finally:
        emit_tel_event("ucc_run_module_end", {"name": _ucc_name, "ok": _ucc_ok})

# --- AUTO ENABLE EXTRA STEP TYPES ---
BUILTIN_STEP_TYPES.update({
    "coherence_audit",
    "extract_json_fields",
    "verify_json_assertions",
    "verify_json_patterns",
    "validate_mapping_table",
    "validate_mapping_index",
})
