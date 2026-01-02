from __future__ import annotations

import argparse
import csv
from pathlib import Path

import numpy as np


def deriv(state: np.ndarray, p: dict) -> np.ndarray:
    # state = [u_r, u_i, phi, phi_dot]
    u_r, u_i, phi, phi_dot = state
    alpha = p["alpha"]
    beta = p["beta"]
    g1 = p["g1"]
    g2 = p["g2"]
    m2 = p["m2"]

    u_mag_sq = u_r * u_r + u_i * u_i

    # CGL-like
    du_r = (-alpha * u_r + beta * u_i) - (u_r * u_mag_sq) + (g1 * phi * u_r)
    du_i = (-alpha * u_i - beta * u_r) - (u_i * u_mag_sq) + (g1 * phi * u_i)

    # KG-like for phi
    dphi = phi_dot
    dphi_dot = -m2 * phi + g2 * u_mag_sq

    return np.array([du_r, du_i, dphi, dphi_dot], dtype=float)


def rk4_step(state: np.ndarray, dt: float, p: dict) -> np.ndarray:
    k1 = deriv(state, p)
    k2 = deriv(state + 0.5 * dt * k1, p)
    k3 = deriv(state + 0.5 * dt * k2, p)
    k4 = deriv(state + dt * k3, p)
    return state + (dt / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--T", type=float, default=50.0, help="total time")
    ap.add_argument("--dt", type=float, default=0.01, help="time step")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", type=str, default="python/experiments/cglkg_toy/out/cglkg_seed0.csv")
    ap.add_argument("--alpha", type=float, default=1.0)
    ap.add_argument("--beta", type=float, default=0.15)
    ap.add_argument("--g1", type=float, default=0.8)
    ap.add_argument("--g2", type=float, default=0.8)
    ap.add_argument("--m2", type=float, default=1.0)
    args = ap.parse_args()

    if args.dt <= 0:
        raise SystemExit("dt must be > 0")
    if args.T <= args.dt:
        raise SystemExit("T must be > dt")

    rng = np.random.default_rng(args.seed)

    p = {"alpha": args.alpha, "beta": args.beta, "g1": args.g1, "g2": args.g2, "m2": args.m2}

    # Initial conditions (small perturbation)
    u_r0 = 0.1 + 0.01 * rng.standard_normal()
    u_i0 = 0.0 + 0.01 * rng.standard_normal()
    phi0 = 0.1 + 0.01 * rng.standard_normal()
    phi_dot0 = 0.0

    state = np.array([u_r0, u_i0, phi0, phi_dot0], dtype=float)

    n = int(args.T / args.dt)
    t = 0.0

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    with out_path.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["t_s", "u_r", "u_i", "phi", "phi_dot", "u_mag_sq"])
        for _ in range(n + 1):
            u_r, u_i, phi, phi_dot = state
            u_mag_sq = u_r * u_r + u_i * u_i
            w.writerow([t, u_r, u_i, phi, phi_dot, u_mag_sq])

            # step
            state = rk4_step(state, args.dt, p)
            t += args.dt

            # basic safety: stop if NaN/Inf
            if not np.isfinite(state).all():
                break

    print(f"Wrote: {out_path.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())