#!/usr/bin/env python3
from __future__ import annotations
import argparse, json, math, statistics
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Tuple

REPO = Path(__file__).resolve().parents[2]

def load(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def clamp01(x: float) -> float:
    return max(0.0, min(1.0, float(x)))

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

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--telemetry", required=True, help="Path to telemetry.json")
    ap.add_argument("--perturbations", required=False, help="Path to perturbations.json (optional)")
    ap.add_argument("--out", required=True, help="Output state_estimate.json")
    args = ap.parse_args()

    telemetry_path = Path(args.telemetry)
    tel = load(telemetry_path)

    pert_path = Path(args.perturbations) if args.perturbations else (telemetry_path.parent / "perturbations.json")
    pert = load(pert_path) if pert_path.exists() else None

    m = tel.get("metrics", {})
    mean = {
        "E": clamp01(float(m.get("E", 1.0))),
        "T": clamp01(float(m.get("T", 1.0))),
        "Psi": clamp01(float(m.get("Psi", 1.0))),
        "DeltaS": float(m.get("DeltaS", 0.0)),
        "Lambda": clamp01(float(m.get("Lambda", 0.0))),
        "Es": clamp01(float(m.get("Es", 1.0))),
    }

    # Sigma from perturbation ensemble (if present)
    sigma = {"E":0.0,"T":0.0,"Psi":0.0,"DeltaS":0.0,"Lambda":0.0,"Es":0.0}
    corr = {}

    if pert and isinstance(pert.get("perturbations"), list) and pert.get("base"):
        samples = [pert["base"]["metrics"]] + [p["metrics"] for p in pert["perturbations"] if "metrics" in p]
        keys = ["E","T","Psi","Es"]
        for k in keys:
            xs = [float(s.get(k, mean[k])) for s in samples]
            sigma[k] = stddev(xs)

        # DeltaS/Lambda sigma from drift list if available
        drifts = [float(p.get("drift_from_base", 0.0)) for p in pert.get("perturbations", [])]
        sigma["DeltaS"] = stddev(drifts)
        sigma["Lambda"] = stddev(drifts)
        sigma["Es"] = stddev([float(s.get("Es", mean["Es"])) for s in samples])

        # correlations
        series = {k:[float(s.get(k, mean[k])) for s in samples] for k in keys}
        corr["E,T"] = pearson(series["E"], series["T"])
        corr["E,Psi"] = pearson(series["E"], series["Psi"])
        corr["T,Psi"] = pearson(series["T"], series["Psi"])
        corr["DeltaS,Lambda"] = pearson(drifts, drifts) if len(drifts) >= 2 else 0.0

    # contradiction: how much Psi deviates from E*T (scaled, clamped)
    et = mean["E"] * mean["T"]
    contradiction = clamp01(abs(mean["Psi"] - et) * 10.0)

    # risk bands (B then A then C)
    ethical_band = band(mean["Es"], yellow=0.90, red=0.80, higher_is_worse=False)
    lambda_band  = band(mean["Lambda"], yellow=0.10, red=0.20, higher_is_worse=True)
    trace_band   = band(mean["T"], yellow=0.90, red=0.80, higher_is_worse=False)

    recommendations = []
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
        "notes": "B then A then C: Es first, then Lambda, then T"
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[state_estimator] wrote {out_path}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
