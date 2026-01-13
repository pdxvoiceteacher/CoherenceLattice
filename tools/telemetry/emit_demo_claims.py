#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict, List


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("telemetry_json", help="Path to telemetry.json to annotate with demo claim(s)")
    ap.add_argument("--repo-root", default=".", help="Repo root (for relative evidence paths)")
    ap.add_argument("--mode", default="method_provenance", choices=["method_provenance"], help="Which demo claim set to emit")
    args = ap.parse_args()

    tele = Path(args.telemetry_json).resolve()
    doc = json.loads(tele.read_text(encoding="utf-8"))

    artifacts = doc.get("artifacts") or []
    pert = None
    for a in artifacts:
        p = str(a.get("path", ""))
        if p.replace("\\", "/").endswith("perturbations.json"):
            pert = p.replace("\\", "/")
            break

    if args.mode == "method_provenance":
        claim = {
            "id": "claim_demo_method_perturbations_v1",
            "type": "method",
            "statement": "DeltaS and Lambda in telemetry.metrics were derived from perturbations.json drift distances for this run.",
            "confidence": 0.95,
            "evidence": [pert] if pert else [],
            "assumptions": [
                "perturbations.json encodes the drift distances used to compute DeltaS/Lambda in run_wrapper"
            ],
            "notes": "Demo claim: provenance-only (does not assert scientific truth, only derivation lineage)."
        }
    else:
        raise SystemExit(f"Unknown mode: {args.mode}")

    claims = doc.get("claims")
    if claims is None:
        doc["claims"] = [claim]
    else:
        # Append if not already present by id
        if not any(c.get("id") == claim["id"] for c in claims):
            claims.append(claim)

    tele.write_text(json.dumps(doc, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(f"[emit_demo_claims] updated {tele}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
