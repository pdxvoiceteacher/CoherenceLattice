from __future__ import annotations

import csv
import json
import statistics
from pathlib import Path
from typing import Any, Dict, Tuple, List

import yaml
from jsonschema import Draft202012Validator

from .audit import AuditBundle, env_info, now_utc_iso, sha256_file, write_bundle


BUILTIN_STEP_TYPES = {
    "ingest_json",
    "ingest_csv",
    "compute_lambdaT",
    "threshold_flags",
    "emit_report",
    "emit_threshold_table",
    "compare_tches_runs",
}


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


def compute_lambdaT(series: list[float], dt_s: float, dT_design_C: float, tau_res_s: float) -> Dict[str, float]:
    if dt_s <= 0:
        raise ValueError("dt_s must be > 0")
    if len(series) < 2:
        raise ValueError("temperature series must have at least 2 samples")

    dTdt = [(series[i] - series[i-1]) / dt_s for i in range(1, len(series))]
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
    ts = []
    for row in rows:
        if t_col not in row:
            continue
        ts.append(float(row[t_col]))
    if len(ts) < 2:
        raise ValueError("Cannot infer dt_s: need at least 2 time samples in CSV")
    diffs = [ts[i] - ts[i-1] for i in range(1, len(ts))]
    diffs = [d for d in diffs if d > 0]
    if not diffs:
        raise ValueError("Cannot infer dt_s: non-positive time diffs in CSV")
    return float(statistics.median(diffs))


def emit_threshold_table(
    outdir: Path,
    metrics: Dict[str, Any],
    flags: Dict[str, Any],
    thresholds: Dict[str, Any],
    name_csv: str = "thresholds.csv",
    name_md: str = "thresholds.md",
) -> List[Path]:
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


def _col_floats(rows: List[Dict[str, str]], col: str) -> List[float]:
    out = []
    for r in rows:
        if col in r and r[col] != "":
            out.append(float(r[col]))
    return out


def summarize_tches_csv(rows: List[Dict[str, str]], thresholds: Dict[str, Any]) -> Dict[str, Any]:
    warnL = float(thresholds.get("lambdaT_warn", 0.7))
    alarmL = float(thresholds.get("lambdaT_alarm", 1.0))
    warnE = float(thresholds.get("E_warn", 0.8))
    alarmE = float(thresholds.get("E_alarm", 0.6))
    warnT = float(thresholds.get("T_warn", 0.85))
    alarmT = float(thresholds.get("T_alarm", 0.7))
    warnPsiTE = float(thresholds.get("PsiTE_warn", 0.7))
    alarmEs = float(thresholds.get("Es_alarm", 0.8))

    lam = _col_floats(rows, "Lambda_T")
    E = _col_floats(rows, "E_model")
    T = _col_floats(rows, "T_transparency")
    PsiTE = _col_floats(rows, "Psi_TE")
    Es = _col_floats(rows, "Es_site")
    Ppump = _col_floats(rows, "P_pump_kW")
    Qch = _col_floats(rows, "Q_chiller_kW")

    def safe_min(xs): return min(xs) if xs else float("nan")
    def safe_mean(xs): return (sum(xs)/len(xs)) if xs else float("nan")
    def safe_max(xs): return max(xs) if xs else float("nan")

    warn_L_steps = sum(1 for x in lam if x > warnL)
    alarm_L_steps = sum(1 for x in lam if x > alarmL)

    warn_E_steps = sum(1 for x in E if x < warnE)
    alarm_E_steps = sum(1 for x in E if x < alarmE)

    warn_T_steps = sum(1 for x in T if x < warnT)
    alarm_T_steps = sum(1 for x in T if x < alarmT)

    warn_Psi_steps = sum(1 for x in PsiTE if x < warnPsiTE)
    alarm_Es_steps = sum(1 for x in Es if x < alarmEs)

    return {
        "max_LambdaT": safe_max(lam),
        "mean_LambdaT": safe_mean(lam),
        "warn_LambdaT_steps": warn_L_steps,
        "alarm_LambdaT_steps": alarm_L_steps,
        "min_E": safe_min(E),
        "warn_E_steps": warn_E_steps,
        "alarm_E_steps": alarm_E_steps,
        "min_T": safe_min(T),
        "warn_T_steps": warn_T_steps,
        "alarm_T_steps": alarm_T_steps,
        "min_PsiTE": safe_min(PsiTE),
        "warn_PsiTE_steps": warn_Psi_steps,
        "min_Es": safe_min(Es),
        "alarm_Es_steps": alarm_Es_steps,
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

    # deltas (baseline - lambda) for “improvement” when positive
    delta_warn = base["warn_LambdaT_steps"] - lam["warn_LambdaT_steps"]
    delta_alarm = base["alarm_LambdaT_steps"] - lam["alarm_LambdaT_steps"]

    metrics: Dict[str, Any] = {
        "baseline_path": str(baseline_path),
        "lambda_path": str(lambda_path),
        "baseline_sha256": sha256_file(baseline_path),
        "lambda_sha256": sha256_file(lambda_path),

        **{f"baseline_{k}": v for k, v in base.items()},
        **{f"lambda_{k}": v for k, v in lam.items()},

        "delta_warn_LambdaT_steps": delta_warn,
        "delta_alarm_LambdaT_steps": delta_alarm,
        "delta_mean_Ppump": lam["mean_Ppump"] - base["mean_Ppump"],
        "delta_mean_Qch": lam["mean_Qch"] - base["mean_Qch"],
    }

    flags: Dict[str, Any] = {
        "improved_warn_time": (delta_warn > 0),
        "baseline_alarm": (base["alarm_LambdaT_steps"] > 0),
        "lambda_alarm": (lam["alarm_LambdaT_steps"] > 0),
    }

    # Emit comparison markdown + json
    outdir.mkdir(parents=True, exist_ok=True)
    p_md = outdir / "comparison.md"
    p_js = outdir / "comparison.json"

    p_js.write_text(json.dumps({"metrics": metrics, "flags": flags}, indent=2, sort_keys=True), encoding="utf-8")

    p_md.write_text(
        "\n".join([
            "# TCHES Run Comparison (baseline vs lambda)\n",
            f"- baseline: `{baseline_path}`",
            f"- lambda: `{lambda_path}`",
            "",
            "## Key outcomes",
            f"- baseline warn_LambdaT_steps: **{base['warn_LambdaT_steps']}**",
            f"- lambda warn_LambdaT_steps: **{lam['warn_LambdaT_steps']}**",
            f"- delta (baseline - lambda): **{delta_warn}**  (positive means lambda reduced warn-time)",
            f"- delta mean pump power (lambda - baseline): **{metrics['delta_mean_Ppump']:.4g}** kW",
            f"- delta mean chiller load (lambda - baseline): **{metrics['delta_mean_Qch']:.4g}** kW",
            "",
            "## Summary table",
            "| metric | baseline | lambda | delta |",
            "|---|---:|---:|---:|",
            f"| warn_LambdaT_steps | {base['warn_LambdaT_steps']} | {lam['warn_LambdaT_steps']} | {delta_warn} |",
            f"| alarm_LambdaT_steps | {base['alarm_LambdaT_steps']} | {lam['alarm_LambdaT_steps']} | {delta_alarm} |",
            f"| max_LambdaT | {base['max_LambdaT']:.6g} | {lam['max_LambdaT']:.6g} | {(lam['max_LambdaT']-base['max_LambdaT']):.6g} |",
            f"| mean_LambdaT | {base['mean_LambdaT']:.6g} | {lam['mean_LambdaT']:.6g} | {(lam['mean_LambdaT']-base['mean_LambdaT']):.6g} |",
            f"| mean_Ppump | {base['mean_Ppump']:.6g} | {lam['mean_Ppump']:.6g} | {metrics['delta_mean_Ppump']:.6g} |",
            f"| mean_Qch | {base['mean_Qch']:.6g} | {lam['mean_Qch']:.6g} | {metrics['delta_mean_Qch']:.6g} |",
            "",
            "## Integrity hashes",
            f"- baseline_sha256: `{metrics['baseline_sha256']}`",
            f"- lambda_sha256: `{metrics['lambda_sha256']}`",
            "",
        ]),
        encoding="utf-8",
    )

    return metrics, flags, [p_md, p_js]


def run_module(module_path: Path, input_path: Path, outdir: Path, schema_path: Path) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    module_doc = load_yaml(module_path)
    schema_doc = load_schema(schema_path)
    validate_module(module_doc, schema_doc)

    mod = module_doc["module"]
    thresholds = mod.get("thresholds", {})

    context: Dict[str, Any] = {
        "input_path": str(input_path),
        "input": None,
        "metrics": {},
        "flags": {},
        "report": None,
        "output_files": []
    }

    for step in module_doc["steps"]:
        stype = step["type"]
        params = step.get("params", {}) or {}

        if stype == "ingest_json":
            context["input"] = load_json(input_path)

        elif stype == "ingest_csv":
            context["input"] = load_csv_table(input_path)

        elif stype == "compute_lambdaT":
            if context["input"] is None:
                raise ValueError("compute_lambdaT requires prior ingest step")

            dT_design = float(params.get("dT_design_C", 20.0))
            tau_res = float(params.get("tau_res_s", 120.0))

            src = context["input"]
            if isinstance(src, dict):
                series_key = str(params.get("series_key", "T_block_C"))
                dt_key = str(params.get("dt_key", "dt_s"))
                series = [float(x) for x in src[series_key]]
                dt_s = float(src[dt_key])

            elif isinstance(src, list):
                series_col = str(params.get("series_col", "T_block_C"))
                t_col = str(params.get("t_col", "t_s"))
                dt_s = float(params["dt_s"]) if "dt_s" in params else _infer_dt_from_tcol(src, t_col)
                series = [float(row[series_col]) for row in src]

            else:
                raise ValueError("Unsupported input type for compute_lambdaT")

            out = compute_lambdaT(series, dt_s, dT_design, tau_res)
            context["metrics"].update(out)

        elif stype == "threshold_flags":
            context["flags"].update(threshold_flags(context["metrics"], thresholds))

        elif stype == "compare_tches_runs":
            if context["input"] is None or not isinstance(context["input"], dict):
                raise ValueError("compare_tches_runs requires ingest_json of a config dict")
            task_dir = Path(input_path).parent
            m, fl, outs = compare_tches_runs(task_dir, context["input"], outdir, thresholds)
            context["metrics"].update(m)
            context["flags"].update(fl)
            context["output_files"].extend(outs)

        elif stype == "emit_report":
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
            context["report"] = str(report_path)
            context["output_files"].append(report_path)

        elif stype == "emit_threshold_table":
            name_csv = str(params.get("name_csv", "thresholds.csv"))
            name_md = str(params.get("name_md", "thresholds.md"))
            outs = emit_threshold_table(outdir, context["metrics"], context["flags"], thresholds, name_csv, name_md)
            context["output_files"].extend(outs)

        else:
            raise ValueError(f"Unsupported step type: {stype}")

    module_sha = sha256_file(module_path)
    input_sha = sha256_file(input_path)

    outputs = {}
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