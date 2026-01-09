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
    ap.add_argument("--prev-state", default="", help="optional previous state_estimate.json for hysteresis")
    ap.add_argument("--prev-decision", default="", help="optional previous control_decision.json for hysteresis")
    ap.add_argument("--allow-recover-from-halt", action="store_true", help="allow leaving halt if thresholds recover (default false)")
    args = ap.parse_args()

    s = load(Path(args.state))
    mean = s["mean"]

    Es = float(mean["Es"])
    Lam = float(mean["Lambda"])
    T = float(mean["T"])

    # Enter/exit thresholds (hysteresis)
    ES_ENTER = 0.80
    ES_EXIT  = 0.85

    LAM_Y_ENTER = 0.10
    LAM_Y_EXIT  = 0.08
    LAM_R_ENTER = 0.20

    T_R_ENTER = 0.80
    T_R_EXIT  = 0.85

    # Base decision (B then A then C)
    decision = "continue"
    gates = {"consent_required": False, "human_review_required": False, "strict_mode": False}
    actions = []

    if Es < ES_ENTER:
        decision = "escalate"
        gates = {"consent_required": True, "human_review_required": True, "strict_mode": True}
        actions.append({"type":"invoke_ucc_module","id":"coherence.audit.strict.v0","why":"Es below enter threshold"})
        actions.append({"type":"consent_gate","why":"ethical band red"})
    elif Lam >= LAM_R_ENTER:
        decision = "halt"
        gates = {"consent_required": True, "human_review_required": True, "strict_mode": True}
        actions.append({"type":"increase_perturbations","n":5,"why":"Lambda critical"})
        actions.append({"type":"invoke_ucc_module","id":"coherence.audit.strict.v0","why":"Lambda red"})
    elif Lam >= LAM_Y_ENTER:
        decision = "slow"
        gates = {"consent_required": False, "human_review_required": False, "strict_mode": True}
        actions.append({"type":"increase_perturbations","n":5,"why":"Lambda yellow"})
    elif T < T_R_ENTER:
        decision = "reroute"
        gates = {"consent_required": False, "human_review_required": False, "strict_mode": True}
        actions.append({"type":"tighten_traceability","to":0.90,"why":"T below enter threshold"})
        actions.append({"type":"invoke_ucc_module","id":"coherence.audit.strict.v0","why":"T red"})

    # --- Hysteresis using previous decision/state (optional) ---
    prev_decision = ""
    if args.prev_decision:
        try:
            prev_decision = load(Path(args.prev_decision)).get("decision","")
        except Exception:
            prev_decision = ""
    elif args.prev_state:
        # If you only have prev-state, you can approximate from prev risk band later; leave blank for now
        prev_decision = ""

    hysteresis_note = ""

    if prev_decision == "halt" and not args.allow_recover_from_halt:
        # Never auto-recover from halt without explicit permission
        decision = "halt"
        gates = {"consent_required": True, "human_review_required": True, "strict_mode": True}
        actions = [{"type":"human_review","why":"previous decision was halt; auto-recover disabled"}]
        hysteresis_note = "held halt (no auto-recover)"
    elif prev_decision == "escalate" and decision != "escalate":
        # Require stronger Es recovery to exit escalate
        if Es < ES_EXIT:
            decision = "escalate"
            gates = {"consent_required": True, "human_review_required": True, "strict_mode": True}
            actions.append({"type":"consent_gate","why":"hysteresis: Es not recovered to exit threshold"})
            hysteresis_note = "held escalate until Es>=0.85"
    elif prev_decision == "slow" and decision == "continue":
        # Require Lambda to drop below exit threshold to leave slow
        if Lam >= LAM_Y_EXIT:
            decision = "slow"
            gates = {"consent_required": False, "human_review_required": False, "strict_mode": True}
            actions.append({"type":"increase_perturbations","n":5,"why":"hysteresis: Lambda not below exit threshold"})
            hysteresis_note = "held slow until Lambda<0.08"
    elif prev_decision == "reroute" and decision == "continue":
        # Require T to recover above exit threshold
        if T < T_R_EXIT:
            decision = "reroute"
            gates = {"consent_required": False, "human_review_required": False, "strict_mode": True}
            actions.append({"type":"tighten_traceability","to":0.90,"why":"hysteresis: T not recovered to exit threshold"})
            hysteresis_note = "held reroute until T>=0.85"

    out = {
        "schema_id":"coherencelattice.control_decision.v1",
        "version":1,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "decision": decision,
        "gates": gates,
        "actions": actions,
        "notes": "Policy order: B(Es) then A(Lambda) then C(T). " + (("Hysteresis: " + hysteresis_note) if hysteresis_note else "")
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[policy] wrote {out_path}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
