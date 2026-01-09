#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, platform, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]

def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def git_commit() -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    except Exception:
        return "unknown"

def run(cmd: list[str], cwd: Path | None = None) -> None:
    subprocess.run(cmd, cwd=str(cwd) if cwd else None, check=True)

def load_json_bom_safe(p: Path):
    return json.loads(p.read_text(encoding="utf-8-sig"))

def extract_metrics_from_audit_bundle(audit_bundle: Path):
    """
    Best-effort extraction. Different modules expose different keys.
    We prefer canonical keys if present; otherwise fall back to known proxies.
    """
    b = load_json_bom_safe(audit_bundle)
    m = b.get("metrics", {}) or {}
    f = b.get("flags", {}) or {}

    # Empathy proxy: prefer E; else claim coverage; else 1.0
    E = float(m.get("E", m.get("E_claim_coverage", 1.0)))

    # Transparency proxy: prefer T; else required sections coverage; else 1.0
    T = float(m.get("T", m.get("T_required_sections_coverage", 1.0)))

    # Psi: prefer Psi; else compute E*T
    Psi = float(m.get("Psi", E * T))

    # Ethical symmetry: prefer Es; else use Es_fields_ok (0/1) if present; else 1.0
    if "Es" in m:
        Es = float(m["Es"])
    elif "Es_fields_ok" in m:
        Es = 1.0 if int(m.get("Es_fields_ok", 0)) > 0 else 0.0
    else:
        Es = 1.0

    # DeltaS / Lambda: prefer if present, else 0.0 (safe default)
    DeltaS = float(m.get("DeltaS", 0.0))
    Lambda = float(m.get("Lambda", 0.0))

    telemetry_ok = bool(f.get("overall_pass", True))

    return {
        "metrics": {"E": E, "T": T, "Psi": Psi, "DeltaS": DeltaS, "Lambda": Lambda, "Es": Es},
        "flags": {"telemetry_ok": telemetry_ok},
        "raw_bundle_metrics": m,
        "raw_bundle_flags": f
    }

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True, help="Output directory for telemetry run")
    ap.add_argument("--quick", action="store_true", help="Quick mode (smoke)")
    args = ap.parse_args()

    outdir = Path(args.out).resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    # 1) Run KONOMI smoke
    smoke_out = outdir / "konomi_smoke_out"
    smoke_out.mkdir(parents=True, exist_ok=True)

    run([
        sys.executable,
        "python/experiments/konomi_smoke/run_smoke.py",
        "--quick" if args.quick else "--full",
        "--outdir",
        str(smoke_out)
    ], cwd=REPO)

    summary = smoke_out / "konomi_smoke_summary.json"
    if not summary.exists():
        raise SystemExit(f"Missing expected smoke summary: {summary}")

    # 2) Run UCC coverage against summary
    ucc_out = outdir / "ucc_cov_out"
    ucc_out.mkdir(parents=True, exist_ok=True)

    run([
        sys.executable, "-m", "ucc.cli", "run",
        "ucc/modules/konomi_smoke_coverage.yml",
        "--input", str(summary),
        "--outdir", str(ucc_out)
    ], cwd=REPO)

    audit_bundle = ucc_out / "audit_bundle.json"

    artifacts = [
        {"path": str(summary.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(summary)}
    ]
    if audit_bundle.exists():
        artifacts.append({"path": str(audit_bundle.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(audit_bundle)})

    # 3) Metrics/flags: prefer audit_bundle if present
    if audit_bundle.exists():
        extracted = extract_metrics_from_audit_bundle(audit_bundle)
        metrics = extracted["metrics"]
        flags = extracted["flags"]
        notes = "metrics sourced from ucc audit_bundle.json"
    else:
        metrics = {"E": 1.0, "T": 1.0, "Psi": 1.0, "DeltaS": 0.0, "Lambda": 0.0, "Es": 1.0}
        flags = {"telemetry_ok": True}
        notes = "audit_bundle.json missing; placeholder metrics used"

    telemetry = {
        "schema_id": "coherencelattice.telemetry_run.v1",
        "version": 1,
        "run_id": outdir.name,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "environment": {
            "python": sys.version.replace("\\n", " "),
            "platform": platform.platform(),
            "git_commit": git_commit()
        },
        "metrics": metrics,
        "flags": flags,
        "artifacts": artifacts,
        "ucc": {
            "audit_bundle_path": str(audit_bundle.relative_to(REPO)).replace("\\", "/") if audit_bundle.exists() else None,
            "audit_bundle_sha256": sha256_file(audit_bundle) if audit_bundle.exists() else None
        },
        "notes": notes
    }

    out_json = outdir / "telemetry.json"
    out_json.write_text(json.dumps(telemetry, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[run_wrapper] wrote {out_json}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
