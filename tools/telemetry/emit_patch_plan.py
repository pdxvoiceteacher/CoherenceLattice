#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

REPO = Path(__file__).resolve().parents[2]
SCHEMA_ID = "coherencelattice.change_patch_plan.v1"

def load(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()

def norm_path(p: Path) -> str:
    try:
        rp = p.resolve()
        # prefer relative-to-repo when possible
        return rp.relative_to(REPO).as_posix()
    except Exception:
        return p.as_posix()

def plan_for_action(action: str) -> Dict[str, Any]:
    a = action.lower().strip()
    # deterministic hints by action family
    if "noop" in a or "maintain_green" in a:
        return {
            "targets": ["tests/baselines/*", ".github/workflows/ci.yml", "scripts/make_uvlm_bundle.ps1"],
            "suggested_edits": [
                "No code change required.",
                "Only update baselines intentionally if metrics changed for a justified reason.",
                "Ensure CI workflow remains canonical and non-duplicated.",
                "Generate and upload UVLM bundle after merge."
            ],
            "tests_required": ["pytest -q python/tests", "pytest -q ucc/tests", "telemetry smoke in CI"],
            "safety_notes": ["Keep policy gates intact (Es->Lambda->T).", "Do not bypass audit/validators."]
        }
    if "increase_perturbations" in a or "perturb" in a:
        return {
            "targets": ["tools/telemetry/run_wrapper.py", ".github/workflows/ci.yml"],
            "suggested_edits": [
                "Increase --perturbations count in CI telemetry smoke step.",
                "Confirm ΔS/Λ thresholds remain non-flaky after change."
            ],
            "tests_required": ["CI telemetry smoke", "validate_run.py gates", "compare_runs.py"],
            "safety_notes": ["Higher perturbations increases runtime; avoid excessive CI time."]
        }
    if "tighten_traceability" in a or "trace" in a:
        return {
            "targets": ["tools/telemetry/validate_run.py", "tools/telemetry/policy.py", "ucc/modules/*"],
            "suggested_edits": [
                "Adjust T-related thresholds conservatively.",
                "Ensure disclosure/audit modules remain enabled.",
                "Document rationale in receipt + rollback."
            ],
            "tests_required": ["pytest -q ucc/tests", "CI telemetry + policy gates"],
            "safety_notes": ["Do not reduce transparency to improve performance.", "Preserve audit trails."]
        }
    if "tighten_ethics" in a or "ethics" in a:
        return {
            "targets": ["tools/telemetry/policy.py", "ucc/modules/*", "governance/risk/*"],
            "suggested_edits": [
                "Adjust Es thresholds or add UCC strict module invocation on yellow band.",
                "Add/extend risk registry entries if new risk class introduced.",
                "Ensure consent gates trigger on ethical red band."
            ],
            "tests_required": ["pytest -q ucc/tests", "policy gate in CI"],
            "safety_notes": ["Ethical symmetry (Es) is a first-class invariant; never weaken it."]
        }
    # default fallback
    return {
        "targets": ["(manual review)"],
        "suggested_edits": [
            "No known mapping for this action; determine target files manually.",
            "Update proposal with explicit targets/diff hints if needed."
        ],
        "tests_required": ["pytest -q python/tests", "pytest -q ucc/tests", "CI telemetry smoke"],
        "safety_notes": ["Keep changes minimal; add tests for any new behavior."]
    }

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--proposal", required=True, help="Path to change_proposal.json")
    ap.add_argument("--out", required=True, help="Output change_patch_plan.json path")
    args = ap.parse_args()

    proposal_path = Path(args.proposal)
    prop = load(proposal_path)
    basis = prop.get("basis", {}) or {}

    changes = prop.get("changes", []) or []
    items = []
    for ch in changes:
        cid = str(ch.get("id",""))
        action = str(ch.get("action",""))
        priority = str(ch.get("priority","low"))
        why = str(ch.get("why",""))
        hint = plan_for_action(action)
        # allow proposal-specified targets if present
        targets = ch.get("targets") or hint["targets"]
        if not targets:
            targets = hint["targets"]
        items.append({
            "id": cid or "chg-unknown",
            "action": action or "unknown",
            "priority": priority if priority in ("low","medium","high") else "low",
            "why": why or "(no rationale provided)",
            "targets": list(targets) if isinstance(targets, list) else [str(targets)],
            "suggested_edits": hint["suggested_edits"],
            "tests_required": hint["tests_required"],
            "safety_notes": hint["safety_notes"],
            "expected_effects": ch.get("expected_effects", {}) or {}
        })

    plan = {
        "schema_id": SCHEMA_ID,
        "version": 1,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "proposal": {"path": norm_path(proposal_path), "sha256": sha256_file(proposal_path)},
        "basis": {
            "telemetry_sha256": str(basis.get("telemetry_sha256","")),
            "state_sha256": str(basis.get("state_sha256","")),
            "decision_sha256": str(basis.get("decision_sha256",""))
        },
        "items": items,
        "notes": "Diff-hints only (proposal-only). No auto-apply."
    }

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(plan, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[emit_patch_plan] wrote {outp}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
