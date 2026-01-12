#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict, List, Tuple


def load_metrics(p: Path) -> Dict[str, float]:
    doc = json.loads(p.read_text(encoding="utf-8"))
    m = doc.get("metrics", doc)
    out: Dict[str, float] = {}
    for k, v in (m or {}).items():
        try:
            out[k] = float(v)
        except Exception:
            pass
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("baseline")
    ap.add_argument("candidate")
    ap.add_argument("--nondecreasing", default="Psi,E,T,Es")
    ap.add_argument("--nonincreasing", default="Lambda,DeltaS")
    ap.add_argument("--eps", type=float, default=1e-4)
    ap.add_argument("--out", default="out/reject_reason.json")
    args = ap.parse_args()

    b = load_metrics(Path(args.baseline))
    c = load_metrics(Path(args.candidate))

    nondec = [k.strip() for k in args.nondecreasing.split(",") if k.strip()]
    noninc = [k.strip() for k in args.nonincreasing.split(",") if k.strip()]
    eps = float(args.eps)

    violations: List[Dict[str, Any]] = []

    def check(metric: str, rule: str) -> None:
        if metric not in b or metric not in c:
            return
        bv = float(b[metric])
        cv = float(c[metric])
        delta = cv - bv

        if rule == "nondecreasing":
            if cv + eps < bv:
                violations.append({"metric": metric, "rule": rule, "baseline": bv, "candidate": cv, "delta": delta, "eps": eps})
        elif rule == "nonincreasing":
            if cv - eps > bv:
                violations.append({"metric": metric, "rule": rule, "baseline": bv, "candidate": cv, "delta": delta, "eps": eps})

    for k in nondec:
        check(k, "nondecreasing")
    for k in noninc:
        check(k, "nonincreasing")

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)

    decision = "accept" if not violations else "reject"
    payload = {
        "schema": "plasticity_reject_reason_v1",
        "decision": decision,
        "eps": eps,
        "baseline": str(Path(args.baseline)),
        "candidate": str(Path(args.candidate)),
        "violations": violations,
    }
    outp.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(f"[explain_compare] wrote {outp} decision={decision} violations={len(violations)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
