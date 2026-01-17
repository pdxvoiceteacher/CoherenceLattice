#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys

REPO_ROOT = Path(__file__).resolve().parents[2]
SRC_PATH = REPO_ROOT / "python" / "src"
if SRC_PATH.exists() and str(SRC_PATH) not in sys.path:
    sys.path.insert(0, str(SRC_PATH))

from coherence_sim.model import ADJ, State, classify, tau0


def regime_label(r: int) -> str:
    return f"S{r}"


def build_state_from_psi(psi: float) -> State:
    psi = max(0.0, min(psi, 1.0))
    root = math.sqrt(psi)
    return State(E=root, T=root)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="out/demo_no_teleport.json")
    ap.add_argument("--steps", type=int, default=12)
    ap.add_argument("--delta", type=float, default=0.05, help="Per-step psi increment (<= tau0/2 recommended)")
    ap.add_argument("--start-psi", type=float, default=0.35)
    ap.add_argument("--direction", choices=["up", "down"], default="up")
    args = ap.parse_args()

    step_delta = args.delta if args.direction == "up" else -args.delta
    if abs(step_delta) > (tau0 / 2.0 + 1e-12):
        raise SystemExit(f"delta {args.delta} exceeds tau0/2={tau0/2:.3f}; may violate no-teleport assumptions")

    rows = []
    psi = args.start_psi
    prev_state = build_state_from_psi(psi)
    prev_regime = classify(prev_state)

    rows.append({
        "step": 0,
        "psi": round(psi, 6),
        "regime": regime_label(prev_regime),
        "adjacent_from_prev": True,
    })

    ok = True
    for i in range(1, args.steps + 1):
        psi = max(0.0, min(1.0, psi + step_delta))
        state = build_state_from_psi(psi)
        regime = classify(state)
        adjacent = regime in ADJ[prev_regime]
        ok = ok and adjacent

        rows.append({
            "step": i,
            "psi": round(psi, 6),
            "regime": regime_label(regime),
            "adjacent_from_prev": adjacent,
        })

        prev_state = state
        prev_regime = regime

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema": "demo_no_teleport_v1",
        "params": {
            "steps": args.steps,
            "delta": args.delta,
            "start_psi": args.start_psi,
            "direction": args.direction,
            "tau0": tau0,
        },
        "path": rows,
        "adjacency_ok": ok,
    }
    out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    if not ok:
        raise SystemExit("No-teleport check failed: non-adjacent regime transition detected")

    print(f"[demo_no_teleport] wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
