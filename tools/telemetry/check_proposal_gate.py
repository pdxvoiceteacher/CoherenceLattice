#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, subprocess, sys
from pathlib import Path
from typing import Any, Dict, List

REPO = Path(__file__).resolve().parents[2]
APPROVED_DIR = REPO / "governance" / "proposals" / "approved"

PROTECTED_PREFIXES = [
    "ucc/src/",
    "tools/telemetry/",
    "schema/telemetry/",
    ".github/workflows/",
]

def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=str(REPO), text=True).strip()

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

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", required=True, help="base ref e.g. origin/master")
    ap.add_argument("--head", default="HEAD")
    ap.add_argument("--state", required=True, help="out/telemetry_smoke/state_estimate.json")
    ap.add_argument("--decision", required=True, help="out/telemetry_smoke/control_decision.json")
    args = ap.parse_args()

    changed = git("diff", "--name-only", f"{args.base}...{args.head}").splitlines()
    changed = [c.strip() for c in changed if c.strip()]

    protected_changed = any(any(c.startswith(p) for p in PROTECTED_PREFIXES) for c in changed)

    if not protected_changed:
        print("[proposal_gate_v2_1] OK: no protected-path changes")
        return 0

    state_p = (REPO / args.state).resolve()
    dec_p = (REPO / args.decision).resolve()
    if not state_p.exists() or not dec_p.exists():
        print("[proposal_gate_v2_1] FAIL: state/decision artifacts missing.")
        print("Expected:", state_p, dec_p)
        return 2

    st = load(state_p)
    dec = load(dec_p)

    want_state = state_digest(st)
    want_dec = decision_digest(dec)

    if not APPROVED_DIR.exists():
        print("[proposal_gate_v2_1] FAIL: approved proposal directory missing:", APPROVED_DIR)
        return 2

    approved_files = sorted(APPROVED_DIR.glob("*.json"))
    if not approved_files:
        print("[proposal_gate_v2_1] FAIL: no approved proposals present.")
        print("Add an approved proposal in governance/proposals/approved/ that matches the current run.")
        return 2

    matches = []
    for fp in approved_files:
        try:
            pdoc = load(fp)
            basis = pdoc.get("basis", {}) or {}
            ps = str(basis.get("state_sha256",""))
            pd = str(basis.get("decision_sha256",""))
            if ps == want_state and pd == want_dec:
                matches.append(fp)
        except Exception:
            continue

    if not matches:
        print("[proposal_gate_v2_1] FAIL: no approved proposal matches current decision/state digests.")
        print("Wanted state_sha256 :", want_state)
        print("Wanted decision_sha256:", want_dec)
        print("Approved proposals checked:", len(approved_files))
        print("TIP: Promote a proposal generated from this run into governance/proposals/approved/ (via PR).")
        return 2

    print("[proposal_gate_v2_1] OK: matching approved proposal found:")
    for fp in matches[:5]:
        print(" -", fp.relative_to(REPO).as_posix())
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
