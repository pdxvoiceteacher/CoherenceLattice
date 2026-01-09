#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict

def load(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def sha256_bytes(b: bytes) -> str:
    h = hashlib.sha256()
    h.update(b)
    return h.hexdigest()

def canonical_sha(obj: Any) -> str:
    s = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return sha256_bytes(s.encode("utf-8"))

def decision_digest(dec: dict) -> str:
    # drop volatile fields; keep policy-relevant content
    return canonical_sha({
        "schema_id": dec.get("schema_id",""),
        "version": dec.get("version", 1),
        "decision": dec.get("decision",""),
        "gates": dec.get("gates", {}) or {},
        "actions": dec.get("actions", []) or []
    })

def state_digest(state: dict) -> str:
    mean = state.get("mean", {}) or {}
    rb = state.get("risk_band", {}) or {}

    # Policy depends on Es, Lambda, T. Round to stabilize cross-machine variance.
    def r3(x: float) -> float:
        try:
            return round(float(x), 3)
        except Exception:
            return 0.0

    core = {
        "schema_id": state.get("schema_id",""),
        "version": state.get("version", 1),
        "mean": {
            "Es": r3(mean.get("Es", 1.0)),
            "Lambda": r3(mean.get("Lambda", 0.0)),
            "T": r3(mean.get("T", 1.0))
        },
        "risk_band": {
            "ethical": rb.get("ethical",""),
            "lambda": rb.get("lambda",""),
            "traceability": rb.get("traceability","")
        }
    }
    return canonical_sha(core)

def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-dir", required=True)
    ap.add_argument("--telemetry", required=True)
    ap.add_argument("--state", required=True)
    ap.add_argument("--decision", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--git-commit", default="")
    args = ap.parse_args()

    run_dir = Path(args.run_dir)
    tel_p = Path(args.telemetry)
    st_p  = Path(args.state)
    dec_p = Path(args.decision)

    tel = load(tel_p)
    st  = load(st_p)
    dec = load(dec_p)

    # Recommendations become proposed changes (proposal-only, no auto apply)
    changes = []
    recs = st.get("recommendations", []) or []
    for i, r in enumerate(recs, start=1):
        changes.append({
            "id": f"chg-{i:03d}",
            "action": r.get("action","unknown"),
            "priority": r.get("priority","medium"),
            "why": r.get("why",""),
            "targets": [],
            "diff_hint": "",
            "risk_ids": [],
            "expected_effects": {}
        })

    if not changes:
        changes.append({
            "id": "chg-001",
            "action": "noop_maintain_green",
            "priority": "low",
            "why": "System is green; maintain baselines and keep telemetry consistent.",
            "targets": ["tests/baselines/*", ".github/workflows/ci.yml"],
            "diff_hint": "No changes required; only update baselines intentionally when expected.",
            "risk_ids": [],
            "expected_effects": {"goal":"stability"}
        })

    proposal = {
        "schema_id": "coherencelattice.change_proposal.v1",
        "version": 1,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "basis": {
            "run_dir": str(run_dir).replace("\\","/"),
            "git_commit": args.git_commit,
            # keep telemetry file hash (raw)
            "telemetry_sha256": sha256_file(tel_p),
            # state/decision hashes are canonical digests (stable across machines)
            "state_sha256": state_digest(st),
            "decision_sha256": decision_digest(dec)
        },
        "decision": dec,
        "changes": changes,
        "notes": "Proposal-only. No auto-apply. Requires human/CI review per governance. v2.1 uses canonical digests."
    }

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(proposal, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[propose_change] wrote {outp}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
