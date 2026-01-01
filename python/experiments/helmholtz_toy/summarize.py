from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from pathlib import Path
import numpy as np

FIELDS = ["L_pde", "Lambda", "E", "T", "Psi"]

def ffloat(x: str):
    x = (x or "").strip()
    if x == "" or x.lower() == "none":
        return None
    return float(x)

def mean_std(xs: list[float]):
    if len(xs) == 0:
        return (None, None)
    if len(xs) == 1:
        return (float(xs[0]), 0.0)
    arr = np.array(xs, dtype=np.float64)
    return (float(arr.mean()), float(arr.std(ddof=1)))

def fmt(m, s):
    if m is None:
        return ""
    if s is None:
        return f"{m:.4g}"
    return f"{m:.4g} ± {s:.3g}"

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--infile", type=str, required=True)
    ap.add_argument("--outdir", type=str, required=True)
    args = ap.parse_args()

    in_path = Path(args.infile)
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    # group[(scenario,t)][field] -> list[float]
    group = defaultdict(lambda: defaultdict(list))
    counts = defaultdict(int)

    with in_path.open("r", newline="") as f:
        r = csv.DictReader(f)
        for row in r:
            scenario = row["scenario"]
            t = int(row["t"])
            key = (scenario, t)
            counts[key] += 1
            for fld in FIELDS:
                v = ffloat(row.get(fld, ""))
                if v is not None:
                    group[key][fld].append(v)

    # sorted keys: scenario then descending t (5..1)
    keys = sorted(counts.keys(), key=lambda k: (k[0], -k[1]))

    # write summary.csv
    out_csv = outdir / "summary_by_step.csv"
    with out_csv.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["scenario", "t", "n",
                    "L_pde_mean", "L_pde_std",
                    "Lambda_mean", "Lambda_std",
                    "E_mean", "E_std",
                    "T_mean", "T_std",
                    "Psi_mean", "Psi_std"])
        for (scenario, t) in keys:
            n = counts[(scenario, t)]
            vals = {}
            for fld in FIELDS:
                m, s = mean_std(group[(scenario, t)][fld])
                vals[fld] = (m, s)
            w.writerow([
                scenario, t, n,
                vals["L_pde"][0], vals["L_pde"][1],
                vals["Lambda"][0], vals["Lambda"][1],
                vals["E"][0], vals["E"][1],
                vals["T"][0], vals["T"][1],
                vals["Psi"][0], vals["Psi"][1],
            ])

    # write summary.md (human-readable)
    out_md = outdir / "summary_by_step.md"
    with out_md.open("w", encoding="utf-8") as f:
        f.write("# Helmholtz Toy Summary (guided vs unguided)\n\n")
        f.write(f"Input: `{in_path.as_posix()}`\n\n")
        f.write("| scenario | t | n | L_pde | Lambda | E | T | Psi |\n")
        f.write("|---|---:|---:|---:|---:|---:|---:|---:|\n")
        for (scenario, t) in keys:
            n = counts[(scenario, t)]
            row = []
            for fld in FIELDS:
                m, s = mean_std(group[(scenario, t)][fld])
                row.append(fmt(m, s))
            f.write(f"| {scenario} | {t} | {n} | {row[0]} | {row[1]} | {row[2]} | {row[3]} | {row[4]} |\n")

    # also compute guided - unguided delta Psi by t (mean difference)
    deltas = []
    for t in sorted({k[1] for k in counts.keys()}, reverse=True):
        g = group.get(("guided", t), {}).get("Psi", [])
        u = group.get(("unguided", t), {}).get("Psi", [])
        if len(g) and len(u):
            dg = np.mean(g) - np.mean(u)
            deltas.append((t, float(dg)))

    out_md2 = outdir / "delta_psi_guided_minus_unguided.md"
    with out_md2.open("w", encoding="utf-8") as f:
        f.write("# ΔPsi (guided − unguided) by step\n\n")
        f.write("| t | mean(Psi_guided) − mean(Psi_unguided) |\n")
        f.write("|---:|---:|\n")
        for t, d in deltas:
            f.write(f"| {t} | {d:.4g} |\n")

    print(f"Wrote:\n- {out_csv}\n- {out_md}\n- {out_md2}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
