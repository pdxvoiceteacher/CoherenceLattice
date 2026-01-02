from __future__ import annotations

import argparse
import csv
from pathlib import Path

import numpy as np


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--infile", type=str, required=True)
    ap.add_argument("--outmd", type=str, default="")
    args = ap.parse_args()

    in_path = Path(args.infile)
    rows = []
    with in_path.open("r", newline="") as f:
        r = csv.DictReader(f)
        for row in r:
            rows.append(row)

    t = np.array([float(r["t_s"]) for r in rows], dtype=float)
    u = np.array([float(r["u_mag_sq"]) for r in rows], dtype=float)
    phi = np.array([float(r["phi"]) for r in rows], dtype=float)
    phid = np.array([float(r["phi_dot"]) for r in rows], dtype=float)

    dt = float(np.median(np.diff(t))) if len(t) > 2 else float("nan")
    du = np.diff(u) / dt if (len(u) > 2 and np.isfinite(dt) and dt > 0) else np.array([])

    stats = {
        "n": int(len(t)),
        "dt_s": dt,
        "max_u_mag_sq": float(np.max(u)),
        "mean_u_mag_sq": float(np.mean(u)),
        "std_u_mag_sq": float(np.std(u)),
        "max_abs_du_dt": float(np.max(np.abs(du))) if du.size else float("nan"),
        "max_abs_phi": float(np.max(np.abs(phi))),
        "max_abs_phi_dot": float(np.max(np.abs(phid))),
        "final_u_mag_sq": float(u[-1]),
    }

    md = [
        "# CGL–KG Toy Summary\n",
        f"- file: `{in_path}`",
        f"- n: {stats['n']}, dt_s≈{stats['dt_s']:.6g}",
        "",
        "## Key stats",
        f"- max u_mag_sq: {stats['max_u_mag_sq']:.6g}",
        f"- mean u_mag_sq: {stats['mean_u_mag_sq']:.6g}",
        f"- std u_mag_sq: {stats['std_u_mag_sq']:.6g}",
        f"- max |du_mag_sq/dt|: {stats['max_abs_du_dt']:.6g}",
        f"- max |phi|: {stats['max_abs_phi']:.6g}",
        f"- max |phi_dot|: {stats['max_abs_phi_dot']:.6g}",
        f"- final u_mag_sq: {stats['final_u_mag_sq']:.6g}",
        "",
        "Note: This is a toy dynamical system used as a stability testbed (not a consciousness model).",
        "",
    ]
    md_text = "\n".join(md)

    if args.outmd:
        outmd = Path(args.outmd)
        outmd.parent.mkdir(parents=True, exist_ok=True)
        outmd.write_text(md_text, encoding="utf-8")
        print(f"Wrote: {outmd.resolve()}")
    else:
        print(md_text)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())