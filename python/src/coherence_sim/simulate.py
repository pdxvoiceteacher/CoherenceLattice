from __future__ import annotations

import argparse
import csv
from pathlib import Path

from coherence_sim import (
    State, DeltaSynInput,
    psi, classify, valid_transition,
    stepPsi, stepET, traj, regime_path, tau0
)

def main() -> int:
    ap = argparse.ArgumentParser(description="Coherence Lattice simulator (mirrors Lean caps/clamps).")
    ap.add_argument("--steps", type=int, default=50)
    ap.add_argument("--mode", choices=["psi", "et"], default="et")

    ap.add_argument("--E0", type=float, default=0.4)
    ap.add_argument("--T0", type=float, default=0.5)

    ap.add_argument("--lam", type=float, default=0.2)
    ap.add_argument("--mu", type=float, default=0.8)
    ap.add_argument("--gradH", type=float, default=0.0)
    ap.add_argument("--Es", type=float, default=1.0)

    ap.add_argument("--eta", type=float, default=0.1)      # for stepPsi
    ap.add_argument("--etaE", type=float, default=0.1)     # for stepET
    ap.add_argument("--etaT", type=float, default=0.1)

    ap.add_argument("--out", type=str, default="sim.csv")
    args = ap.parse_args()

    s0 = State(E=args.E0, T=args.T0)
    p = DeltaSynInput(lam=args.lam, mu=args.mu, gradH=args.gradH, Es=args.Es)

    if args.mode == "psi":
        f = lambda s: stepPsi(args.eta, p, s)
    else:
        f = lambda s: stepET(args.etaE, args.etaT, p, s)

    xs = traj(f, args.steps, s0)
    rs = regime_path(xs)

    out_path = Path(args.out).resolve()
    with out_path.open("w", newline="") as fp:
        w = csv.writer(fp)
        w.writerow(["t", "E", "T", "psi", "regime"])
        for i, s in enumerate(xs):
            w.writerow([i, s.E, s.T, psi(s), rs[i]])

    # quick validation: every step should be valid_transition if using stepET/stepPsi as defined
    ok = True
    for i in range(len(xs) - 1):
        if not valid_transition(xs[i], xs[i + 1]):
            ok = False
            print(f"WARNING: invalid transition at t={i}: r{rs[i]} -> r{rs[i+1]}  |Δψ|={abs(psi(xs[i+1])-psi(xs[i]))}")
            break

    print(f"Wrote: {out_path}")
    print(f"Steps: {args.steps}  Mode: {args.mode}  All transitions valid: {ok}")
    print(f"Note: tau0={tau0} ; stepET guarantees |Δψ| <= tau0/2 by construction (up to float rounding).")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())