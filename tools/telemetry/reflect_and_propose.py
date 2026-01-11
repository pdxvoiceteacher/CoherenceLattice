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
    # Prefer coherence_metrics if present; else fall back to a shallow scan.
    cm = telemetry.get("coherence_metrics")
    if isinstance(cm, dict):
        return cm

    # Shallow scan for a dict containing likely keys
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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-dir", required=True, help="Run output directory containing telemetry.json")
    ap.add_argument("--out-proposals-dir", required=True, help="Directory to write proposals")
    ap.add_argument("--proposal-id", default="", help="Override proposal id for deterministic runs (e.g. CI)")
    ap.add_argument("--created-at-utc", default="", help="Override created_at_utc (e.g. CI)")
    ap.add_argument("--force-proposal", action="store_true", help="Always emit a proposal (for CI / pipeline checks)")
    ap.add_argument("--min-psi", type=float, default=0.90, help="Trigger if Psi is below this threshold")
    ap.add_argument("--emit-reflection", action="store_true", help="Also write reflection_summary.json into run dir")
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

    ucc_errors = [e for e in ucc_events if isinstance(e, dict) and str(e.get("kind","")).endswith("_error")]
    triggers: Dict[str, Any] = {
        "force_proposal": bool(args.force_proposal),
        "ucc_errors_present": len(ucc_errors) > 0,
        "psi_below_threshold": (psi is not None and psi < float(args.min_psi)),
        "min_psi_threshold": float(args.min_psi),
        "psi_observed": psi,
    }

    recommendations: List[Dict[str, Any]] = []
    if triggers["ucc_errors_present"]:
        recommendations.append({
            "id": "ucc_errors_review",
            "kind": "human_review",
            "target": "ucc",
            "suggestion": "Review UCC step errors and adjust module configuration or governance rules if needed.",
            "rationale": "UCC emitted one or more *_error events during run.",
            "evidence": {"ucc_errors_total": len(ucc_errors)},
        })
    if triggers["psi_below_threshold"]:
        recommendations.append({
            "id": "psi_low_investigate",
            "kind": "diagnostic",
            "target": "telemetry.coherence_metrics.Psi",
            "suggestion": "Investigate low Psi; consider increasing perturbations/samples and reviewing recent changes.",
            "rationale": "Psi fell below configured threshold for tuning triggers.",
            "evidence": {"psi": psi, "min_psi": float(args.min_psi)},
        })

    no_action = (not args.force_proposal) and (len(recommendations) == 0)

    created_at = args.created_at_utc.strip() or _now_utc_iso()

    # Deterministic-ish proposal_id if not provided
    base_for_id = {
        "telemetry_path": str(telemetry_path).replace("\\", "/"),
        "metrics": metrics,
        "tel_summary": tel_summary,
        "counts": {
            "tel_events_total": len(tel_events),
            "ucc_events_total": len(ucc_events),
            "ucc_errors_total": len(ucc_errors),
        },
        "triggers": triggers,
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
            "event_counts": {
                "tel_events_total": len(tel_events),
                "ucc_events_total": len(ucc_events),
                "ucc_errors_total": len(ucc_errors),
            },
            "tel_summary": tel_summary,
        },
        "triggers": triggers,
        "recommendations": recommendations,
        "no_action": bool(no_action),
    }

    out_dir = Path(args.out_proposals_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"tuning_proposal_{pid}.json"
    out_path.write_text(json.dumps(proposal, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
                        encoding="utf-8", newline="\n")

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
