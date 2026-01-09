#!/usr/bin/env python3
from __future__ import annotations
import argparse, json
from datetime import datetime, timezone
from pathlib import Path

def load(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--state", required=True, help="state_estimate.json")
    ap.add_argument("--out", required=True, help="control_decision.json")
    args = ap.parse_args()

    s = load(Path(args.state))
    mean = s["mean"]

    Es = float(mean["Es"])
    Lam = float(mean["Lambda"])
    T = float(mean["T"])

    # Default thresholds (tune later)
    ES_RED = 0.80
    LAM_RED = 0.20
    LAM_YEL = 0.10
    T_RED = 0.80

    decision = "continue"
    gates = {"consent_required": False, "human_review_required": False, "strict_mode": False}
    actions = []

    # B then A then C
    if Es < ES_RED:
        decision = "escalate"
        gates = {"consent_required": True, "human_review_required": True, "strict_mode": True}
        actions.append({"type":"invoke_ucc_module","id":"coherence.audit.strict.v0","why":"Es below threshold"})
        actions.append({"type":"consent_gate","why":"ethical band red"})
    elif Lam >= LAM_RED:
        decision = "halt"
        gates = {"consent_required": True, "human_review_required": True, "strict_mode": True}
        actions.append({"type":"increase_perturbations","n":5,"why":"Lambda critical"})
        actions.append({"type":"invoke_ucc_module","id":"coherence.audit.strict.v0","why":"Lambda red"})
    elif Lam >= LAM_YEL:
        decision = "slow"
        gates = {"consent_required": False, "human_review_required": False, "strict_mode": True}
        actions.append({"type":"increase_perturbations","n":5,"why":"Lambda yellow"})
    elif T < T_RED:
        decision = "reroute"
        gates = {"consent_required": False, "human_review_required": False, "strict_mode": True}
        actions.append({"type":"tighten_traceability","to":0.90,"why":"T below threshold"})
        actions.append({"type":"invoke_ucc_module","id":"coherence.audit.strict.v0","why":"T red"})

    out = {
        "schema_id":"coherencelattice.control_decision.v1",
        "version":1,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "decision": decision,
        "gates": gates,
        "actions": actions,
        "notes": "Policy order: B(Es) then A(Lambda) then C(T)"
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[policy] wrote {out_path}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
