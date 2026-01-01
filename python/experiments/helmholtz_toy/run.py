from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path
import math
import numpy as np

import torch
import torch.nn.functional as F


# ---------- core math ----------

def laplacian_2d(x: torch.Tensor, dx: float, dy: float) -> torch.Tensor:
    k = torch.tensor([[0.0, 1.0, 0.0],
                      [1.0, -4.0, 1.0],
                      [0.0, 1.0, 0.0]], device=x.device, dtype=x.dtype).view(1, 1, 3, 3)
    C = x.shape[1]
    kC = k.repeat(C, 1, 1, 1)
    xpad = F.pad(x, (1, 1, 1, 1), mode="constant", value=0.0)
    lap = F.conv2d(xpad, kC, groups=C)
    return lap / (dx * dx)


def helmholtz_residual(
    x: torch.Tensor,
    inv_v2: torch.Tensor,
    omega: float,
    u0: torch.Tensor,
    delta_m: torch.Tensor,
    dx: float,
    dy: float,
) -> torch.Tensor:
    lap = laplacian_2d(x, dx, dy)
    k2 = (omega ** 2) * inv_v2
    return lap + k2 * x + (omega ** 2) * delta_m * u0


def pde_losses(
    x: torch.Tensor,
    inv_v2: torch.Tensor,
    omega: float,
    u0: torch.Tensor,
    delta_m: torch.Tensor,
    dx: float,
    dy: float,
) -> tuple[torch.Tensor, torch.Tensor]:
    """
    (L_mean, L_opt)
      L_mean = mean(r^2)            (stable for exp(-L) and Λ)
      L_opt  = L_mean * (H*W)       (used for gradients; discourages trivial shrink)
    """
    r = helmholtz_residual(x, inv_v2, omega, u0, delta_m, dx, dy)
    L_mean = (r ** 2).mean()
    H, W = r.shape[-2], r.shape[-1]
    L_opt = L_mean * (H * W)
    return L_mean, L_opt


def track01(x: torch.Tensor, x_ref: torch.Tensor, eps: float = 1e-12) -> float:
    """
    Reference-tracking proxy in (0,1]:
      E = exp( - mse(x, x_ref) / (mse(x,0) + mse(x_ref,0) + eps) )
    Uses float64 internally; robust against scaling.
    """
    x64 = x.double()
    r64 = x_ref.double()
    mse = ((x64 - r64) ** 2).mean()
    energy = (x64 ** 2).mean() + (r64 ** 2).mean() + eps
    ratio = mse / energy
    ratio = torch.nan_to_num(ratio, nan=1e6, posinf=1e6, neginf=1e6)
    return float(torch.exp(-ratio).clamp(0.0, 1.0).item())


def compute_lambda_series(losses: list[float], window: int = 3, eps: float = 1e-9) -> list[float | None]:
    if window < 3:
        raise ValueError("window should be >=3 for meaningful lag-1 correlation")

    sig2: list[float | None] = []
    rho1: list[float | None] = []

    for i in range(len(losses)):
        if i < window - 1:
            sig2.append(None)
            rho1.append(None)
            continue

        w = np.array(losses[i - window + 1 : i + 1], dtype=np.float64)
        v = float(np.var(w, ddof=1))
        a = w[:-1] - w.mean()
        b = w[1:] - w.mean()
        denom = float(np.sum(a * a) + eps)
        r = float(np.sum(a * b) / denom)

        sig2.append(v)
        rho1.append(r)

    sig2_vals = [v for v in sig2 if v is not None]
    rho_vals = [abs(r) for r in rho1 if r is not None]
    if not sig2_vals or not rho_vals:
        return [None] * len(losses)

    sig2_bar = float(np.mean(sig2_vals)) + eps
    rho_bar = float(np.mean(rho_vals)) + eps

    lam: list[float | None] = []
    for v, r in zip(sig2, rho1):
        if v is None or r is None:
            lam.append(None)
        else:
            lam.append((v / sig2_bar) + (abs(r) / rho_bar))
    return lam


# ---------- toy problem ----------

def make_velocity(H: int, W: int, v0: float, anomaly_strength: float = 0.25) -> np.ndarray:
    v = np.full((H, W), v0, dtype=np.float32)
    cx, cy = H // 2, W // 2
    r = min(H, W) // 6
    yy, xx = np.ogrid[:H, :W]
    mask = (yy - cx) ** 2 + (xx - cy) ** 2 <= r * r
    v[mask] = v0 * (1.0 - anomaly_strength)
    return v


def make_u0(H: int, W: int, sx: int, sy: int, sigma: float = 6.0) -> np.ndarray:
    yy, xx = np.mgrid[0:H, 0:W]
    d2 = (yy - sx) ** 2 + (xx - sy) ** 2
    u = np.exp(-d2 / (2.0 * sigma * sigma)).astype(np.float32)
    return np.stack([u, np.zeros_like(u)], axis=0)  # [2,H,W]


def ddim_like_step(x: torch.Tensor, t: int) -> torch.Tensor:
    gamma = (t - 1.0) / t
    return gamma * x


def solve_reference_adam(
    inv_v2: torch.Tensor,
    omega: float,
    u0: torch.Tensor,
    delta_m: torch.Tensor,
    iters: int = 400,
    lr: float = 0.15,
    clamp: float = 25.0,
) -> torch.Tensor:
    """
    Stable reference solve: minimize L_mean(x) by Adam.
    """
    B, _, H, W = u0.shape
    x = torch.zeros((B, 2, H, W), dtype=torch.float64, device=u0.device, requires_grad=True)
    opt = torch.optim.Adam([x], lr=lr)

    for _ in range(iters):
        opt.zero_grad(set_to_none=True)
        L_mean, _ = pde_losses(x, inv_v2, omega, u0, delta_m, 1.0, 1.0)
        L_mean.backward()
        torch.nn.utils.clip_grad_norm_([x], 5.0)
        opt.step()
        with torch.no_grad():
            x.clamp_(-clamp, clamp)

    return x.detach()


_PROBLEM_CACHE: dict[tuple, tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]] = {}


def build_problem(H: int, W: int, omega: float, v0: float, device: str):
    key = (H, W, float(omega), float(v0), device)
    if key in _PROBLEM_CACHE:
        return _PROBLEM_CACHE[key]

    v_np = make_velocity(H, W, v0=v0)
    inv_v2 = torch.tensor(1.0 / (v_np ** 2), device=device, dtype=torch.float64).view(1, 1, H, W)
    delta_m = (inv_v2 - (1.0 / (v0 ** 2))).to(torch.float64)

    sx, sy = H // 3, W // 2
    u0_np = make_u0(H, W, sx=sx, sy=sy, sigma=max(4.0, H / 10.0))
    u0 = torch.tensor(u0_np, device=device, dtype=torch.float64).view(1, 2, H, W)

    x_ref = solve_reference_adam(inv_v2, omega, u0, delta_m)

    Lm_ref, _ = pde_losses(x_ref, inv_v2, omega, u0, delta_m, 1.0, 1.0)
    maxabs = float(x_ref.abs().max().detach().cpu().item())
    print(f"Reference solve: L_mean={float(Lm_ref.cpu().item()):.3g}, max|x_ref|={maxabs:.3g}")

    inv_v2_f = inv_v2.float()
    delta_m_f = delta_m.float()
    u0_f = u0.float()
    x_ref_f = x_ref.float()

    _PROBLEM_CACHE[key] = (inv_v2_f, delta_m_f, u0_f, x_ref_f)
    return _PROBLEM_CACHE[key]


@dataclass
class RunResult:
    rows: list[dict]


def run_one(
    seed: int,
    guided: bool,
    steps: int,
    H: int,
    W: int,
    omega: float,
    v0: float,
    eta: float,
    window: int,
    device: str,
) -> RunResult:
    torch.manual_seed(seed)
    np.random.seed(seed)

    inv_v2, delta_m, u0, x_ref = build_problem(H, W, omega, v0, device)

    x = (torch.randn((1, 2, H, W), device=device, dtype=torch.float32) * 0.25).detach()

    losses: list[float] = []
    rows: list[dict] = []

    for t in range(steps, 0, -1):
        x_tilde = ddim_like_step(x, t)

        if guided:
            x_tilde = x_tilde.detach().requires_grad_(True)
            L_mean, L_opt = pde_losses(x_tilde, inv_v2, omega, u0, delta_m, 1.0, 1.0)
            L_opt.backward()
            g = x_tilde.grad.detach()

            eta_try = eta
            with torch.no_grad():
                L0 = float(L_opt.detach().cpu().item())
                for _ in range(12):
                    x_new = (x_tilde.detach() - eta_try * g)
                    _, Lo_new = pde_losses(x_new, inv_v2, omega, u0, delta_m, 1.0, 1.0)
                    if float(Lo_new.cpu().item()) <= L0 + 1e-12:
                        x = x_new.detach()
                        break
                    eta_try *= 0.5
                else:
                    x = x_tilde.detach()

            L_mean_val, _ = pde_losses(x, inv_v2, omega, u0, delta_m, 1.0, 1.0)
            L_val = float(L_mean_val.detach().cpu().item())
        else:
            x = x_tilde.detach()
            L_mean_val, _ = pde_losses(x, inv_v2, omega, u0, delta_m, 1.0, 1.0)
            L_val = float(L_mean_val.detach().cpu().item())

        E = track01(x, x_ref)
        T = float(math.exp(-L_val))
        Psi = E * T

        losses.append(L_val)
        rows.append({
            "seed": seed,
            "scenario": ("guided" if guided else "unguided"),
            "t": t,
            "L_pde": L_val,
            "Lambda": None,
            "E": E,
            "T": T,
            "Psi": Psi,
        })

    lam = compute_lambda_series(losses, window=window)
    for i, lv in enumerate(lam):
        rows[i]["Lambda"] = (float(lv) if lv is not None else None)

    return RunResult(rows=rows)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--steps", type=int, default=25)
    ap.add_argument("--H", type=int, default=64)
    ap.add_argument("--W", type=int, default=64)
    ap.add_argument("--omega", type=float, default=1.0)
    ap.add_argument("--v0", type=float, default=2.0)
    ap.add_argument("--eta", type=float, default=0.25)
    ap.add_argument("--window", type=int, default=3)
    ap.add_argument("--seeds", type=int, default=50)
    ap.add_argument("--out", type=str, default="out/helmholtz_toy_results.csv")
    ap.add_argument("--device", type=str, default="cpu")
    args = ap.parse_args()

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    common = dict(
        steps=args.steps,
        H=args.H,
        W=args.W,
        omega=args.omega,
        v0=args.v0,
        eta=args.eta,
        window=args.window,
        device=args.device,
    )

    all_rows: list[dict] = []
    for seed in range(args.seeds):
        all_rows += run_one(seed=seed, guided=False, **common).rows
        all_rows += run_one(seed=seed, guided=True, **common).rows

    fieldnames = ["seed", "scenario", "t", "L_pde", "Lambda", "E", "T", "Psi"]
    with out_path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for r in all_rows:
            w.writerow(r)

    print(f"Wrote: {out_path.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())