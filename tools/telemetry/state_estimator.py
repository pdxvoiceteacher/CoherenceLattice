#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import statistics
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Tuple

REPO = Path(__file__).resolve().parents[2]

def load_json(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def clamp01(x: float) -> float:
    try:
        return max(0.0, min(1.0, float(x)))
    except Exception:
        return 0.0

def stddev(xs: List[float]) -> float:
    if len(xs) < 2:
        return 0.0
    return float(statistics.pstdev(xs))

def pearson(xs: List[float], ys: List[float]) -> float:
    if len(xs) < 2 or len(ys) < 2 or len(xs) != len(ys):
        return 0.0
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    denx = math.sqrt(sum((x - mx) ** 2 for x in xs))
    deny = math.sqrt(sum((y - my) ** 2 for y in ys))
    if denx == 0 or deny == 0:
        return 0.0
    return float(max(-1.0, min(1.0, num / (denx * deny))))

def band(value: float, yellow: float, red: float, higher_is_worse: bool=False) -> str:
    v = float(value)
    if higher_is_worse:
        if v >= red: return "red"
        if v >= yellow: return "yellow"
        return "green"
    else:
        if v <= red: return "red"
        if v <= yellow: return "yellow"
        return "green"

def mean_of_series(series: List[float]) -> float:
    return float(sum(series) / max(1, len(series)))

def load_history_jsonl(path: Path, window: int) -> List[dict]:
    if not path.exists():
        return []
    try:
        lines = path.read_text(encoding="utf-8-sig").splitlines()
        if window > 0:
            lines = lines[-window:]
        out = []
        for ln in lines:
            ln = ln.strip()
            if not ln:
                continue
            try:
                out.append(json.loads(ln))
            except Exception:
                continue
        return out
    except Exception:
        return []

def extract_obs_from_telemetry(tel: dict) -> Dict[str, float]:
    m = tel.get("metrics", {}) or {}
    return {
        "E": clamp01(float(m.get("E", 1.0))),
        "T": clamp01(float(m.get("T", 1.0))),
        "Psi": clamp01(float(m.get("Psi", 1.0))),
        "DeltaS": float(m.get("DeltaS", 0.0)),
        "Lambda": clamp01(float(m.get("Lambda", 0.0))),
        "Es": clamp01(float(m.get("Es", 1.0))),
    }

def extract_sigma_from_perturbations(pert: dict, fallback: Dict[str, float]) -> Tuple[Dict[str, float], Dict[str, float]]:
    # sigma fields required by schema; start at 0
    sigma = {"E":0.0,"T":0.0,"Psi":0.0,"DeltaS":0.0,"Lambda":0.0,"Es":0.0}
    corr = {}

    if not pert:
        return sigma, corr

    base = pert.get("base", {})
    perts = pert.get("perturbations", []) or []
    if not isinstance(perts, list):
        return sigma, corr

    # Build samples for E/T/Psi/Es from base+perturbations
    samples = []
    if isinstance(base.get("metrics"), dict):
        samples.append(base["metrics"])
    for p in perts:
        if isinstance(p, dict) and isinstance(p.get("metrics"), dict):
            samples.append(p["metrics"])

    keys = ["E","T","Psi","Es"]
    series = {}
    for k in keys:
        xs = []
        for s in samples:
            try:
                xs.append(float(s.get(k, fallback.get(k, 0.0))))
            except Exception:
                xs.append(float(fallback.get(k, 0.0)))
        sigma[k] = stddev(xs)
        series[k] = xs

    # Drift list (repeatability distance)
    drifts = []
    for p in perts:
        try:
            drifts.append(float(p.get("drift_from_base", 0.0)))
        except Exception:
            drifts.append(0.0)

    sigma["DeltaS"] = stddev(drifts)
    sigma["Lambda"] = stddev(drifts)

    # correlations (optional field allowed by schema)
    corr["E,T"] = pearson(series.get("E",[]), series.get("T",[]))
    corr["E,Psi"] = pearson(series.get("E",[]), series.get("Psi",[]))
    corr["T,Psi"] = pearson(series.get("T",[]), series.get("Psi",[]))
    corr["DeltaS,Lambda"] = pearson(drifts, drifts) if len(drifts) >= 2 else 0.0

    return sigma, corr

def history_stats(hist: List[dict]) -> Tuple[Dict[str, float], Dict[str, float], Dict[str, float]]:
    """
    Returns (hist_mean, hist_sigma, hist_corr_score) where:
      - hist_mean: rolling mean of state_mean metrics
      - hist_sigma: rolling stddev of state_mean metrics
      - hist_corr_score: simple correlation indicators (stored as corr-like pairs)
    """
    if not hist:
        return {}, {}, {}

    keys = ["E","T","Psi","DeltaS","Lambda","Es"]
    series: Dict[str, List[float]] = {k: [] for k in keys}

    for r in hist:
        sm = r.get("state_mean") or r.get("telemetry_mean") or {}
        if not isinstance(sm, dict):
            continue
        for k in keys:
            if k in sm:
                try:
                    series[k].append(float(sm[k]))
                except Exception:
                    pass

    hm = {}
    hs = {}
    for k in keys:
        if series[k]:
            hm[k] = mean_of_series(series[k])
            hs[k] = stddev(series[k])

    # correlate only if we have enough samples
    hc = {}
    if len(series.get("E",[])) >= 2 and len(series.get("T",[])) >= 2:
        hc["E,T"] = pearson(series["E"], series["T"])
    if len(series.get("E",[])) >= 2 and len(series.get("Psi",[])) >= 2:
        hc["E,Psi"] = pearson(series["E"], series["Psi"])
    if len(series.get("T",[])) >= 2 and len(series.get("Psi",[])) >= 2:
        hc["T,Psi"] = pearson(series["T"], series["Psi"])
    if len(series.get("DeltaS",[])) >= 2 and len(series.get("Lambda",[])) >= 2:
        hc["DeltaS,Lambda"] = pearson(series["DeltaS"], series["Lambda"])

    return hm, hs, hc

def fuse(obs: Dict[str, float], hist_mean: Dict[str, float], alpha: float) -> Dict[str, float]:
    """
    mean_fused = alpha*obs + (1-alpha)*hist_mean when hist_mean present, else obs.
    """
    out = dict(obs)
    if not hist_mean:
        return out
    for k, ov in obs.items():
        if k in hist_mean:
            try:
                out[k] = float(alpha) * float(ov) + (1.0 - float(alpha)) * float(hist_mean[k])
            except Exception:
                out[k] = ov
    # clamp bounded metrics
    out["E"] = clamp01(out["E"])
    out["T"] = clamp01(out["T"])
    out["Psi"] = clamp01(out["Psi"])
    out["Lambda"] = clamp01(out["Lambda"])
    out["Es"] = clamp01(out["Es"])
    return out

def combine_sigma(pert_sigma: Dict[str, float], hist_sigma: Dict[str, float]) -> Dict[str, float]:
    """
    Combine independent uncertainty sources conservatively: sigma = max(pert_sigma, hist_sigma)
    """
    keys = ["E","T","Psi","DeltaS","Lambda","Es"]
    out = {k: 0.0 for k in keys}
    for k in keys:
        ps = float(pert_sigma.get(k, 0.0))
        hs = float(hist_sigma.get(k, 0.0))
        out[k] = max(ps, hs)
    return out

def main() -> int:
    ap = argparse.ArgumentParser(description="History-aware state estimator (sensor fusion).")
    ap.add_argument("--telemetry", required=True, help="Path to telemetry.json")
    ap.add_argument("--perturbations", default="", help="Path to perturbations.json (optional)")
    ap.add_argument("--history", default="out/history/state_history.jsonl", help="Path to state_history.jsonl (optional)")
    ap.add_argument("--window", type=int, default=50, help="History window (last N records)")
    ap.add_argument("--alpha", type=float, default=0.70, help="Fusion alpha (obs weight). 0.7 default.")
    ap.add_argument("--out", required=True, help="Output state_estimate.json")
    args = ap.parse_args()

    tel = load_json(Path(args.telemetry))
    obs = extract_obs_from_telemetry(tel)

    pert = None
    if args.perturbations:
        p = Path(args.perturbations)
        if p.exists():
            pert = load_json(p)
    else:
        p = Path(args.telemetry).parent / "perturbations.json"
        if p.exists():
            pert = load_json(p)

    pert_sigma, pert_corr = extract_sigma_from_perturbations(pert, obs)

    hist_path = Path(args.history)
    hist = load_history_jsonl(hist_path, args.window)
    hist_mean, hist_sigma, hist_corr = history_stats(hist)

    mean = fuse(obs, hist_mean, args.alpha)
    sigma = combine_sigma(pert_sigma, hist_sigma)

    # Merge correlations (history dominates when present)
    corr = {}
    corr.update(pert_corr)
    corr.update(hist_corr)

    # contradiction: (1) Psi mismatch (2) obs vs fused drift
    et = mean["E"] * mean["T"]
    psi_mismatch = abs(mean["Psi"] - et)

    # scaled drift from observation (not history mean)
    drift = 0.0
    for k in ["E","T","Psi","Es"]:
        drift += abs(float(obs[k]) - float(mean[k]))
    drift = drift / 4.0

    contradiction = clamp01(psi_mismatch * 10.0 + drift * 5.0)

    # risk bands (B then A then C framing, but estimator just reports)
    ethical_band = band(mean["Es"], yellow=0.90, red=0.80, higher_is_worse=False)
    lambda_band  = band(mean["Lambda"], yellow=0.10, red=0.20, higher_is_worse=True)
    trace_band   = band(mean["T"], yellow=0.90, red=0.80, higher_is_worse=False)

    recommendations = []

    # B then A then C: recommend actions in that order
    if ethical_band == "red":
        recommendations.append({"action":"escalate_consent_gate","priority":"high","why":"Es below 0.80 (ethical risk)"})
        recommendations.append({"action":"invoke_ucc_strict_audit","priority":"high","why":"ethical band red"})
    elif ethical_band == "yellow":
        recommendations.append({"action":"tighten_ethics_checks","priority":"medium","why":"Es in yellow band"})

    if lambda_band == "red":
        recommendations.append({"action":"halt_or_human_review","priority":"high","why":"Lambda >= 0.20 (criticality)"})
    elif lambda_band == "yellow":
        recommendations.append({"action":"increase_perturbations","priority":"medium","why":"Lambda in yellow band"})

    if trace_band == "red":
        recommendations.append({"action":"tighten_traceability","priority":"high","why":"T below 0.80"})
    elif trace_band == "yellow":
        recommendations.append({"action":"tighten_traceability","priority":"medium","why":"T in yellow band"})

    # Additional: high variance / contradiction suggestions
    if contradiction >= 0.30:
        recommendations.append({"action":"increase_perturbations","priority":"medium","why":"contradiction elevated; request more repeatability evidence"})
    if sigma.get("Lambda", 0.0) >= 0.05:
        recommendations.append({"action":"slow_and_monitor","priority":"medium","why":"Lambda sigma elevated (history/perturbations)"})
    if sigma.get("Es", 0.0) >= 0.05:
        recommendations.append({"action":"tighten_ethics_checks","priority":"medium","why":"Es variance elevated (history/perturbations)"})

    out = {
        "schema_id": "coherencelattice.state_estimate.v1",
        "version": 1,
        "t": datetime.now(timezone.utc).isoformat(),
        "mean": mean,
        "sigma": sigma,
        "corr": corr,
        "contradiction": contradiction,
        "risk_band": {"ethical": ethical_band, "lambda": lambda_band, "traceability": trace_band},
        "recommendations": recommendations,
        "notes": f"History-aware fusion: window={len(hist)} alpha={args.alpha} history_path={str(hist_path).replace(chr(92),'/') if hist_path.exists() else 'missing'}"
    }

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(out, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[state_estimator] wrote {outp}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
