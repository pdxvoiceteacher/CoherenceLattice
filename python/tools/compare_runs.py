from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict, Optional

def read_json(p: Path) -> Dict[str, Any]:
    return json.loads(p.read_text(encoding="utf-8"))

def resolve_run(repo_root: Path, run_or_path: str) -> Path:
    p = Path(run_or_path)
    if p.exists():
        return p.resolve()
    rd = repo_root / "paper" / "out" / "runs" / run_or_path
    if rd.exists():
        return rd.resolve()
    raise SystemExit(f"run not found: {run_or_path}")

def get_float(x: Any) -> Optional[float]:
    try:
        if x is None:
            return None
        return float(x)
    except Exception:
        return None

def delta_score(mA: Dict[str, Any], mB: Dict[str, Any]) -> Optional[float]:
    a = get_float(mA.get("guft", {}).get("psi"))
    b = get_float(mB.get("guft", {}).get("psi"))
    if a is None or b is None:
        return None
    score = b - a
    okB = bool(mB.get("telemetry_ok", {}).get("all_ok") is True)
    if not okB:
        score -= 1.0
    return score

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("runA")
    ap.add_argument("runB")
    ap.add_argument("--json", dest="json_out", default="", help="write JSON diff to file")
    args = ap.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    dirA = resolve_run(repo_root, args.runA)
    dirB = resolve_run(repo_root, args.runB)

    mA = read_json(dirA / "metrics.json")
    mB = read_json(dirB / "metrics.json")

    out: Dict[str, Any] = {
        "runA": {"run_id": mA.get("run_id"), "dir": str(dirA)},
        "runB": {"run_id": mB.get("run_id"), "dir": str(dirB)},
        "guft": {
            "E_A": mA.get("guft", {}).get("E"),
            "T_A": mA.get("guft", {}).get("T"),
            "psi_A": mA.get("guft", {}).get("psi"),
            "E_B": mB.get("guft", {}).get("E"),
            "T_B": mB.get("guft", {}).get("T"),
            "psi_B": mB.get("guft", {}).get("psi"),
        },
        "telemetry_ok": {
            "A": mA.get("telemetry_ok", {}),
            "B": mB.get("telemetry_ok", {}),
        },
        "delta_score": delta_score(mA, mB),
    }

    print("=== RUN COMPARATOR ===")
    print(f"A: {out['runA']['run_id']}  ({out['runA']['dir']})")
    print(f"B: {out['runB']['run_id']}  ({out['runB']['dir']})")
    print("")
    print("GUFT:")
    print(f"  E:   {out['guft']['E_A']} -> {out['guft']['E_B']}")
    print(f"  T:   {out['guft']['T_A']} -> {out['guft']['T_B']}")
    print(f"  psi: {out['guft']['psi_A']} -> {out['guft']['psi_B']}")
    print("")
    print("telemetry_ok:")
    print(f"  A.all_ok={out['telemetry_ok']['A'].get('all_ok')}  B.all_ok={out['telemetry_ok']['B'].get('all_ok')}")
    print("")
    print(f"delta_score={out['delta_score']}")
    print("")

    if args.json_out:
        Path(args.json_out).write_text(json.dumps(out, indent=2, sort_keys=True), encoding="utf-8")
        print(f"Wrote JSON: {args.json_out}")

    return 0

if __name__ == "__main__":
    raise SystemExit(main())