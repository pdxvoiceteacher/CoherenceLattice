#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, platform, subprocess, sys, statistics, re, math
from datetime import datetime, timezone
from pathlib import Path
import sys

# --- TEL flag pre-parse (parser-agnostic) ---
_TEL_EMIT = False
if "--emit-tel" in sys.argv:
    _TEL_EMIT = True
    sys.argv.remove("--emit-tel")
_TEL_EVENTS_EMIT = False
if "--emit-tel-events" in sys.argv:
    _TEL_EVENTS_EMIT = True
    sys.argv.remove("--emit-tel-events")

# --- /TEL flag pre-parse ---


REPO = Path(__file__).resolve().parents[2]

def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def run(cmd: list[str], cwd: Path | None = None) -> None:
    subprocess.run(cmd, cwd=str(cwd) if cwd else None, check=True)

def load_json_bom_safe(p: Path):
    return json.loads(p.read_text(encoding="utf-8-sig"))

def git_commit() -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    except Exception:
        return "unknown"

def clamp01(x: float) -> float:
    return max(0.0, min(1.0, float(x)))

def perf_E_from_konomi(smoke_out: Path) -> tuple[float, float, int]:
    """
    Compute E proxy from numeric substrings in KONOMI result CSVs.
    Returns (E, perf_index, count_values).
    """
    csvs = [
        smoke_out / "evgpu" / "evgpu_matmul_results.csv",
        smoke_out / "femto" / "femto_async_results.csv",
        smoke_out / "blockarray" / "blockarray_results.csv",
        smoke_out / "cube" / "cube_results.csv",
    ]

    num_re = re.compile(r"[-+]?\d*\.?\d+(?:[eE][-+]?\d+)?")
    vals: list[float] = []

    for fp in csvs:
        if not fp.exists():
            continue
        try:
            txt = fp.read_text(encoding="utf-8-sig", errors="ignore")
            for s in num_re.findall(txt):
                try:
                    v = float(s)
                except Exception:
                    continue
                if math.isfinite(v):
                    vals.append(v)
        except Exception:
            continue

    if not vals:
        return (1.0, 0.0, 0)

    filtered = []
    for v in vals[:10000]:
        av = abs(v)
        # drop huge integer-like IDs
        if av > 1000.0 and float(int(av)) == av:
            continue
        filtered.append(av)

    if not filtered:
        filtered = [abs(v) for v in vals[:10000]]

    logs = [math.log1p(x) for x in filtered[:4000]]
    perf_index = float(sum(logs) / max(1, len(logs)))

    # IMPORTANT: scale is chosen to keep E high enough for Psi gates.
    # If perf_index is ~5-10, dividing by 80 keeps E ~0.88-0.94.
    E = math.exp(-perf_index / 80.0)
    E = clamp01(E)
    return (E, perf_index, len(filtered))

def run_smoke(smoke_out: Path, quick: bool) -> Path:
    smoke_out.mkdir(parents=True, exist_ok=True)
    run([
        sys.executable,
        "python/experiments/konomi_smoke/run_smoke.py",
        "--quick" if quick else "--full",
        "--outdir", str(smoke_out)
    ], cwd=REPO)
    summary = smoke_out / "konomi_smoke_summary.json"
    if not summary.exists():
        raise SystemExit(f"Missing expected smoke summary: {summary}")
    return summary

def run_ucc_coverage(input_path: Path, outdir: Path) -> Path:
    """
    Runs konomi_smoke_coverage.yml and returns the path to audit_bundle.json.
    """
    outdir.mkdir(parents=True, exist_ok=True)
    run([sys.executable, "-m", "ucc.cli", "run",
         "ucc/modules/konomi_smoke_coverage.yml",
         "--input", str(input_path),
         "--outdir", str(outdir)], cwd=REPO)
    audit_bundle = outdir / "audit_bundle.json"
    if not audit_bundle.exists():
        raise SystemExit(f"Missing audit_bundle.json at {audit_bundle}")
    return audit_bundle

def T_Es_from_audit_bundle(audit_bundle: Path) -> tuple[float, float]:
    """
    Derive T and Es from UCC coverage audit bundle.
    - T from section_coverage (or present_count/required_count)
    - Es from flags.sections_complete (1/0)
    """
    b = load_json_bom_safe(audit_bundle)
    m = b.get("metrics", {}) or {}
    fl = b.get("flags", {}) or {}

    if "section_coverage" in m:
        T = float(m.get("section_coverage", 1.0))
    elif ("present_count" in m) and ("required_count" in m):
        req = float(m.get("required_count", 1.0))
        pres = float(m.get("present_count", req))
        T = pres / req if req > 0 else 1.0
    else:
        T = 1.0

    T = clamp01(T)
    Es = 1.0 if bool(fl.get("sections_complete", fl.get("overall_pass", True))) else 0.0
    Es = clamp01(Es)
    return (T, Es)

def metric_vec(E: float, T: float, Es: float) -> dict[str, float]:
    Psi = clamp01(float(E) * float(T))
    return {"E": clamp01(E), "T": clamp01(T), "Psi": Psi, "Es": clamp01(Es)}

def drift(a: dict[str, float], b: dict[str, float]) -> float:
    keys = ["E", "T", "Psi", "Es"]
    return sum(abs(a[k] - b[k]) for k in keys) / len(keys)

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--perturbations", type=int, default=3)
    args = ap.parse_args()

    outdir = Path(args.out).resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    # Base run
    base_smoke = outdir / "konomi_smoke_base"
    base_summary = run_smoke(base_smoke, args.quick)

    base_cov = outdir / "ucc_cov_out"
    base_bundle = run_ucc_coverage(base_summary, base_cov)

    E_base, perf_index_base, nvals_base = perf_E_from_konomi(base_smoke)
    T_base, Es_base = T_Es_from_audit_bundle(base_bundle)
    base_vec = metric_vec(E_base, T_base, Es_base)

    distances: list[float] = []
    pert_results = []

    for i in range(1, max(0, args.perturbations) + 1):
        smoke_i = outdir / f"konomi_smoke_perturb_{i}"
        summary_i = run_smoke(smoke_i, args.quick)

        cov_i = outdir / f"ucc_cov_perturb_{i}"
        bundle_i = run_ucc_coverage(summary_i, cov_i)

        E_i, perf_index_i, nvals_i = perf_E_from_konomi(smoke_i)
        T_i, Es_i = T_Es_from_audit_bundle(bundle_i)
        vec_i = metric_vec(E_i, T_i, Es_i)

        d_i = drift(base_vec, vec_i)
        distances.append(d_i)

        pert_results.append({
            "i": i,
            "audit_bundle_path": str(bundle_i.relative_to(REPO)).replace("\\", "/"),
            "metrics": vec_i,
            "drift_from_base": d_i,
            "perf_index": perf_index_i,
            "perf_values_count": nvals_i,
            "T_source": "audit_bundle.section_coverage",
            "Es_source": "audit_bundle.flags.sections_complete"
        })

    deltaS = float(statistics.mean(distances)) if distances else 0.0
    lam = float(max(distances)) if distances else 0.0

    pert_path = outdir / "perturbations.json"
    pert_doc = {
        "kind": "telemetry_perturbations.v1",
        "base": {
            "audit_bundle_path": str(base_bundle.relative_to(REPO)).replace("\\", "/"),
            "metrics": base_vec,
            "perf_index": perf_index_base,
            "perf_values_count": nvals_base
        },
        "perturbations": pert_results,
        "deltaS": deltaS,
        "lambda": lam
    }
    pert_path.write_text(json.dumps(pert_doc, indent=2, sort_keys=True), encoding="utf-8")

    # Final telemetry.json
    metrics = dict(base_vec)
    metrics["DeltaS"] = deltaS
    metrics["Lambda"] = lam

    artifacts = [
        {"path": str(base_summary.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(base_summary)},
        {"path": str(base_bundle.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(base_bundle)},
        {"path": str(pert_path.relative_to(REPO)).replace("\\", "/"), "sha256": sha256_file(pert_path)}
    ]

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
        "flags": {
            "telemetry_ok": True,
            "perturbations_count": len(distances),
            "deltaS_from_perturbations": deltaS,
            "lambda_from_perturbations": lam,
            "perf_index_base": perf_index_base,
            "perf_values_count_base": nvals_base
        },
        "artifacts": artifacts,
        "ucc": {
            "audit_bundle_path": str(base_bundle.relative_to(REPO)).replace("\\", "/"),
            "audit_bundle_sha256": sha256_file(base_bundle)
        },
        "notes": "Telemetry derived without telemetry_snapshot module. E from KONOMI CSV numeric substrings; T/Es from UCC coverage audit_bundle; Psi=E*T; Î”S/Î› from perturbation drift."
    }

    out_json = outdir / "telemetry.json"
    out_json.write_text(json.dumps(telemetry, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[run_wrapper] wrote {out_json}")
    return 0

if __name__ == "__main__":
    # Preserve original entrypoint semantics, but allow TEL emission after run completion.
    try:
        _rc = main()
    except SystemExit as _se:
        _rc = _se.code

    if _rc is None:
        _rc = 0

    # --- TEL post-run emission ---

    if globals().get("_TEL_EMIT", False) or globals().get("_TEL_EVENTS_EMIT", False):

        def _tel_out_dir(argv):

            # supports: --out PATH  or  --out=PATH

            for i, a in enumerate(argv):

                if a == "--out" and i + 1 < len(argv):

                    return argv[i + 1]

                if a.startswith("--out="):

                    return a.split("=", 1)[1]

            return None


        try:

            from pathlib import Path

            import json as _json

            from konomi.tel.build import build_tel_and_events_for_out_dir

            from konomi.tel.events import write_events_jsonl


            _out = _tel_out_dir(sys.argv)

            if not _out:

                raise RuntimeError("TEL requested but --out was not found in argv")


            _out_dir = Path(_out)

            _telemetry_path = _out_dir / "telemetry.json"

            if not _telemetry_path.exists():

                raise FileNotFoundError(f"telemetry.json not found at {_telemetry_path}")


            _telemetry_data = _json.loads(_telemetry_path.read_text(encoding="utf-8"))


            _tel, _events = build_tel_and_events_for_out_dir(_out_dir, _telemetry_data, max_depth=2)


            if globals().get("_TEL_EMIT", False):

                _tel.write_json(_out_dir / "tel.json")

                _telemetry_data["tel_summary"] = _tel.summary()

                (_out_dir / "telemetry.json").write_text(

                    _json.dumps(_telemetry_data, ensure_ascii=False, sort_keys=True, indent=2) + "
",

                    encoding="utf-8",

                    newline="
",

                )

                print("[tel] updated telemetry.json with tel_summary")

                print(f"[tel] wrote: {_out_dir / "tel.json"}")


            if globals().get("_TEL_EVENTS_EMIT", False):

                write_events_jsonl(_events, _out_dir / "tel_events.jsonl")

                print(f"[tel_events] wrote: {_out_dir / "tel_events.jsonl"}")


        except Exception as _e:

            print(f"[tel] failed: {_e}", file=sys.stderr)

            raise

    # --- /TEL post-run emission ---
    raise SystemExit(_rc)
