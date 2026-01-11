from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List


def _now_utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _canonical(obj: Any) -> str:
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


ALLOW_PREFIXES = ["config/plasticity/", "governance/", "schema/"]
DENY_PREFIXES = [".github/", "tools/", "ucc/", "python/", "config/"]
BUDGET_KEYS = [
    "perturb", "retry", "timeout", "concurrency", "parallel", "workers", "matrix",
    "interval", "freq", "schedule", "max_", "attempt", "budget"
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--proposal", required=True)
    ap.add_argument("--out", required=True, help="Patch plan output path")
    ap.add_argument("--created-at-utc", default="")
    args = ap.parse_args()

    proposal = json.loads(Path(args.proposal).read_text(encoding="utf-8"))
    pid = proposal.get("proposal_id") or hashlib.sha256(_canonical(proposal).encode("utf-8")).hexdigest()[:12]
    created_at = args.created_at_utc.strip() or _now_utc_iso()

    # Minimal v2 safe op: if psi_below_threshold -> LOWER min_psi_threshold by 0.01 (thermo-safe: fewer triggers)
    triggers = proposal.get("triggers") or {}
    psi_low = bool(triggers.get("psi_below_threshold"))

    ops: List[Dict[str, Any]] = []
    if psi_low:
        ops.append({
            "op": "json_set",
            "path": "config/plasticity/tuning.json",
            "json_path": "min_psi_threshold",
            "value": 0.89,
            "note": "Thermo-safe: relax threshold slightly to reduce repeated triggers."
        })

    plan = {
        "schema": "plasticity_patch_plan_v2",
        "proposal_id": pid,
        "created_at_utc": created_at,
        "guardrails": {
            "allow_prefixes": ALLOW_PREFIXES,
            "deny_prefixes": DENY_PREFIXES,
            "budget_keys": BUDGET_KEYS
        },
        "operations": ops
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(plan, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(str(out_path).replace("\\","/"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
