from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional


def _canonical(obj: Any) -> str:
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _now_utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _load_json(p: Path) -> Dict[str, Any]:
    return json.loads(p.read_text(encoding="utf-8"))


def _load_jsonl(p: Path) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    if not p.exists():
        return out
    for ln in p.read_text(encoding="utf-8").splitlines():
        ln = ln.strip()
        if not ln:
            continue
        out.append(json.loads(ln))
    return out


def _find_metrics(telemetry: Dict[str, Any]) -> Dict[str, Any]:
    cm = telemetry.get("coherence_metrics")
    if isinstance(cm, dict):
        return cm

    keys = {"Psi", "E", "T", "Es", "DeltaS", "Lambda"}

    def scan(x: Any) -> Optional[Dict[str, Any]]:
        if isinstance(x, dict):
            if keys.intersection(x.keys()):
                return x
            for v in x.values():
                found = scan(v)
                if found:
                    return found
        elif isinstance(x, list):
            for v in x:
                found = scan(v)
                if found:
                    return found
        return None

    found = scan(telemetry)
    return found if isinstance(found, dict) else {}


def _metric_float(metrics: Dict[str, Any], k: str) -> Optional[float]:
    v = metrics.get(k)
    try:
        return float(v)
    except Exception:
        return None


def _safe_num(x: Any) -> Optional[float]:
    try:
        return float(x)
    except Exception:
        return None



# --- recommendation dedupe (deterministic, thermo-safe) ---
def _action_key(act):
    # Dedupe by actionable signature. Non-action recs dedupe by id.
    if not isinstance(act, dict):
        return None
    op = act.get("op")
    path = act.get("path")
    if op == "json_set":
        jp = act.get("json_path")
        # value is encoded canonically to avoid float repr drift
        try:
            v = json.dumps(act.get("value"), ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        except Exception:
            v = repr(act.get("value"))
        return ("json_set", str(path), str(jp), v)
    if op == "text_replace":
        pat = act.get("pattern")
        rep = act.get("replacement")
        mr = act.get("max_replacements")
        return ("text_replace", str(path), str(pat), str(rep), str(mr))
    return ("op", str(op), str(path))

def _pref_score(rec):
    rid = str(rec.get("id","")).lower()
    # Prefer UCC-error variants if duplicates target the same action
    if "ucc" in rid and "error" in rid:
        return 3
    if "ucc" in rid:
        return 2
    if "psi" in rid:
        return 1
    return 0

def _dedupe_recommendations(recs):
    # Choose the best recommendation per action signature.
    best = {}
    for rec in recs:
        act = rec.get("action_v2") if isinstance(rec, dict) else None
        key = _action_key(act) if isinstance(act, dict) else ("id", str(rec.get("id")) if isinstance(rec, dict) else repr(rec))
        score = _pref_score(rec) if isinstance(rec, dict) else 0
        if key not in best or score > best[key][0]:
            best[key] = (score, rec)

    out = []
    seen = set()
    # Preserve stable order: only emit the chosen item when we encounter it.
    for rec in recs:
        act = rec.get("action_v2") if isinstance(rec, dict) else None
        key = _action_key(act) if isinstance(act, dict) else ("id", str(rec.get("id")) if isinstance(rec, dict) else repr(rec))
        if key in seen:
            continue
        if best[key][1] is rec:
            out.append(rec)
            seen.add(key)
    return out
# --- /recommendation dedupe ---

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-dir", required=True)
    ap.add_argument("--out-proposals-dir", required=True)
    ap.add_argument("--proposal-id", default="")
    ap.add_argument("--created-at-utc", default="")
    ap.add_argument("--force-proposal", action="store_true")
    ap.add_argument("--min-psi", type=float, default=0.90)
    ap.add_argument("--emit-reflection", action="store_true")
    ap.add_argument("--tuning-config", default="config/plasticity/tuning.json")
    ap.add_argument("--tune-step", type=float, default=0.01, help="Thermo-safe decrement step (only decreases)")
    args = ap.parse_args()

    run_dir = Path(args.run_dir)
    telemetry_path = run_dir / "telemetry.json"
    if not telemetry_path.exists():
        raise SystemExit(f"Missing telemetry.json at {telemetry_path}")

    telemetry = _load_json(telemetry_path)
    metrics = _find_metrics(telemetry)
    psi = _metric_float(metrics, "Psi")

    tel_summary = telemetry.get("tel_summary") if isinstance(telemetry.get("tel_summary"), dict) else None

    tel_events_path = run_dir / "tel_events.jsonl"
    ucc_events_path = run_dir / "ucc_tel_events.jsonl"
    tel_events = _load_jsonl(tel_events_path)
    ucc_events = _load_jsonl(ucc_events_path)
    ucc_errors = [e for e in ucc_events if isinstance(e, dict) and str(e.get("kind", "")).endswith("_error")]

    triggers: Dict[str, Any] = {
        "force_proposal": bool(args.force_proposal),
        "ucc_errors_present": len(ucc_errors) > 0,
        "psi_below_threshold": (psi is not None and psi < float(args.min_psi)),
        "min_psi_threshold": float(args.min_psi),
        "psi_observed": psi,
        "tune_step": float(args.tune_step),
    }

    # Load tuning config values
    cfg_path = Path(args.tuning_config)
    cfg = {}
    if cfg_path.exists():
        try:
            cfg = _load_json(cfg_path)
        except Exception:
            cfg = {}

    cfg_min = _safe_num(cfg.get("min_psi_threshold")) or float(args.min_psi)
    cfg_max_props = _safe_num(cfg.get("max_proposals_per_run"))
    cfg_max_sandbox = _safe_num(cfg.get("max_sandbox_attempts"))

    step = max(0.0, float(args.tune_step))

    recommendations: List[Dict[str, Any]] = []

    # 1) Thermo-safe: relax min_psi_threshold (decrease only) when Psi is low
    if triggers["psi_below_threshold"]:
        new_min = max(0.0, cfg_min - step)
        action_v2 = None
        if new_min < cfg_min:
            action_v2 = {
                "op": "json_set",
                "path": "config/plasticity/tuning.json",
                "json_path": "min_psi_threshold",
                "value": new_min,
            }
        recommendations.append({
            "id": "thermo_safe_relax_min_psi",
            "kind": "config_tune",
            "target": "config/plasticity/tuning.json:min_psi_threshold",
            "suggestion": f"Thermo-safe: lower min_psi_threshold by {step:.3f} (from {cfg_min:.3f} to {new_min:.3f}) to reduce repeated tuning triggers.",
            "rationale": "Reduces frequency of tuning loops; does not increase compute budgets.",
            "evidence": {"psi": psi, "configured_min_psi_threshold": cfg_min, "proposed_min_psi_threshold": new_min, "step": step},
            "action_v2": action_v2,
        })

    # 2) Thermo-safe: cap max_sandbox_attempts to 1 if currently >1 (never increases)
    if cfg_max_sandbox is not None and cfg_max_sandbox > 1:
        recommendations.append({
            "id": "thermo_safe_cap_max_sandbox_attempts",
            "kind": "budget_cap",
            "target": "config/plasticity/tuning.json:max_sandbox_attempts",
            "suggestion": f"Thermo-safe: cap max_sandbox_attempts to 1 (from {int(cfg_max_sandbox)}) to avoid repeated sandbox runs.",
            "rationale": "Prevents repeated sandbox cycles and thermodynamic runaway.",
            "evidence": {"current": int(cfg_max_sandbox), "proposed": 1},
            "action_v2": {
                "op": "json_set",
                "path": "config/plasticity/tuning.json",
                "json_path": "max_sandbox_attempts",
                "value": 1,
            },
        })

    # 3) Thermo-safe: cap max_proposals_per_run to 1 if currently >1 when Psi is low
    #    (keeps the original tuning-trigger behavior)
    if cfg_max_props is not None and cfg_max_props > 1 and triggers["psi_below_threshold"]:
        recommendations.append({
            "id": "thermo_safe_cap_max_proposals_per_run",
            "kind": "budget_cap",
            "target": "config/plasticity/tuning.json:max_proposals_per_run",
            "suggestion": f"Thermo-safe: cap max_proposals_per_run to 1 (from {int(cfg_max_props)}) to prevent runaway proposal generation.",
            "rationale": "Hard cap reduces risk of runaway compute / repeated attempts.",
            "evidence": {"current": int(cfg_max_props), "proposed": 1},
            "action_v2": {
                "op": "json_set",
                "path": "config/plasticity/tuning.json",
                "json_path": "max_proposals_per_run",
                "value": 1,
            },
        })

    # 4) NEW: Thermo-safe: cap max_proposals_per_run to 1 whenever UCC errors are present (even if Psi is fine)
    #    Only applies if current value exists and is >1 (a decrease; never introduces new budget keys).
    if cfg_max_props is not None and cfg_max_props > 1 and triggers["ucc_errors_present"]:
        recommendations.append({
            "id": "thermo_safe_cap_max_proposals_on_ucc_error",
            "kind": "budget_cap",
            "target": "config/plasticity/tuning.json:max_proposals_per_run",
            "suggestion": f"Thermo-safe: cap max_proposals_per_run to 1 (from {int(cfg_max_props)}) because UCC errors were observed (even if Psi is fine).",
            "rationale": "When governance errors occur, reduce proposal fan-out to limit runaway loops during unstable control states.",
            "evidence": {"ucc_errors_total": len(ucc_errors), "current": int(cfg_max_props), "proposed": 1},
            "action_v2": {
                "op": "json_set",
                "path": "config/plasticity/tuning.json",
                "json_path": "max_proposals_per_run",
                "value": 1,
            },
        })
    elif triggers["ucc_errors_present"] and cfg_max_props is None:
        # Budget invariant will forbid introducing the key; recommend human change only.
        recommendations.append({
            "id": "thermo_safe_recommend_add_cap_max_proposals_on_ucc_error",
            "kind": "human_review",
            "target": "config/plasticity/tuning.json:max_proposals_per_run",
            "suggestion": "UCC errors observed: ensure max_proposals_per_run exists and is capped at 1 to prevent runaway proposal loops during instability.",
            "rationale": "We avoid auto-introducing budget keys; this is a guided manual recommendation.",
            "evidence": {"ucc_errors_total": len(ucc_errors)},
            "action_v2": None,
        })

    # Human review when UCC errors are present (no auto action)
    if triggers["ucc_errors_present"]:
        recommendations.append({
            "id": "ucc_errors_review",
            "kind": "human_review",
            "target": "ucc",
            "suggestion": "Review UCC *_error events and recent changes; fix root cause before enabling broader plasticity ops.",
            "rationale": "UCC emitted one or more *_error events during run.",
            "evidence": {"ucc_errors_total": len(ucc_errors)},
            "action_v2": None,
        })
    recommendations = _dedupe_recommendations(recommendations)
    no_action = (not args.force_proposal) and (len(recommendations) == 0)
    created_at = args.created_at_utc.strip() or _now_utc_iso()

    base_for_id = {
        "telemetry_path": str(telemetry_path).replace("\\", "/"),
        "metrics": metrics,
        "tel_summary": tel_summary,
        "counts": {"tel_events_total": len(tel_events), "ucc_events_total": len(ucc_events), "ucc_errors_total": len(ucc_errors)},
        "triggers": triggers,
        "recommendations": recommendations,
    }
    pid = args.proposal_id.strip() or hashlib.sha256(_canonical(base_for_id).encode("utf-8")).hexdigest()[:12]

    proposal = {
        "schema": "plasticity_tuning_proposal_v1",
        "proposal_id": pid,
        "created_at_utc": created_at,
        "run_dir": str(run_dir).replace("\\", "/"),
        "inputs": {
            "telemetry_path": str(telemetry_path).replace("\\", "/"),
            "tel_events_path": str(tel_events_path).replace("\\", "/") if tel_events_path.exists() else None,
            "ucc_tel_events_path": str(ucc_events_path).replace("\\", "/") if ucc_events_path.exists() else None,
            "tel_summary_present": bool(tel_summary is not None),
        },
        "measures": {
            "coherence_metrics": metrics,
            "event_counts": {"tel_events_total": len(tel_events), "ucc_events_total": len(ucc_events), "ucc_errors_total": len(ucc_errors)},
            "tel_summary": tel_summary,
        },
        "triggers": triggers,
        "recommendations": recommendations,
        "no_action": bool(no_action),
    }

    out_dir = Path(args.out_proposals_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"tuning_proposal_{pid}.json"
    out_path.write_text(json.dumps(proposal, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n")

    if args.emit_reflection:
        (run_dir / "reflection_summary.json").write_text(
            json.dumps({"proposal_id": pid, "triggers": triggers, "recommendations": recommendations}, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
            encoding="utf-8",
            newline="\n",
        )

    print(str(out_path).replace("\\", "/"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
