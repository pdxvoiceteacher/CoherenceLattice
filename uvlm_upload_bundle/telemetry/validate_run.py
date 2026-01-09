#!/usr/bin/env python3
from __future__ import annotations
import argparse
import json
from pathlib import Path

from jsonschema import Draft202012Validator

REPO = Path(__file__).resolve().parents[2]
SCHEMA = REPO / "schema" / "telemetry" / "telemetry_run.schema.json"

def load_json(p: Path):
    # BOM-safe for Windows-written JSON
    return json.loads(p.read_text(encoding="utf-8-sig"))

def main() -> int:
    ap = argparse.ArgumentParser(description="Validate telemetry.json against schema + optional quality gates.")
    ap.add_argument("telemetry_json", help="Path to telemetry.json (or telemetry_snapshot.json)")

    # Quality gates (optional). If not provided, only schema + Psi=E*T + telemetry_ok is enforced.
    ap.add_argument("--min-e", type=float, default=None)
    ap.add_argument("--min-t", type=float, default=None)
    ap.add_argument("--min-psi", type=float, default=None)
    ap.add_argument("--min-es", type=float, default=None)
    ap.add_argument("--max-lambda", type=float, default=None)
    ap.add_argument("--max-deltas", type=float, default=None)

    # If set, gate violations do not fail the run (schema failures still fail).
    ap.add_argument("--warn-only", action="store_true")

    args = ap.parse_args()

    schema = load_json(SCHEMA)
    data = load_json(Path(args.telemetry_json))

    # 1) Schema validation
    v = Draft202012Validator(schema)
    errors = sorted(v.iter_errors(data), key=lambda e: e.path)
    if errors:
        print("[validate_run] FAIL schema")
        for e in errors[:120]:
            print(" -", list(e.path), e.message)
        return 2

    # 2) Core invariant sanity: Psi ~= E*T (tight check; adjust tolerance if you later store rounded values)
    E = float(data["metrics"]["E"])
    T = float(data["metrics"]["T"])
    Psi = float(data["metrics"]["Psi"])
    if abs(Psi - (E * T)) > 1e-6:
        print(f"[validate_run] FAIL Psi != E*T (Psi={Psi}, E*T={E*T})")
        return 2

    # 3) telemetry_ok must be true
    if not bool(data["flags"]["telemetry_ok"]):
        print("[validate_run] FAIL telemetry_ok=false")
        return 2

    # 4) Optional quality gates
    Es = float(data["metrics"]["Es"])
    Lambda = float(data["metrics"]["Lambda"])
    DeltaS = float(data["metrics"]["DeltaS"])

    gate_failures = []

    def gate(name: str, ok: bool, detail: str):
        if not ok:
            gate_failures.append(f"{name}: {detail}")

    if args.min_e is not None:
        gate("min_e", E >= args.min_e, f"E={E} < {args.min_e}")
    if args.min_t is not None:
        gate("min_t", T >= args.min_t, f"T={T} < {args.min_t}")
    if args.min_psi is not None:
        gate("min_psi", Psi >= args.min_psi, f"Psi={Psi} < {args.min_psi}")
    if args.min_es is not None:
        gate("min_es", Es >= args.min_es, f"Es={Es} < {args.min_es}")
    if args.max_lambda is not None:
        gate("max_lambda", Lambda <= args.max_lambda, f"Lambda={Lambda} > {args.max_lambda}")
    if args.max_deltas is not None:
        gate("max_deltas", abs(DeltaS) <= args.max_deltas, f"|DeltaS|={abs(DeltaS)} > {args.max_deltas}")

    print(f"[validate_run] Metrics: E={E:.3f} T={T:.3f} Psi={Psi:.3f} Es={Es:.3f} DeltaS={DeltaS:.3f} Lambda={Lambda:.3f}")

    if gate_failures:
        print("[validate_run] QUALITY GATE FAILURES:")
        for f in gate_failures:
            print(" -", f)
        if args.warn_only:
            print("[validate_run] WARN-ONLY: continuing despite gate failures")
            return 0
        return 2

    print("[validate_run] OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
