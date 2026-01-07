from __future__ import annotations

import os
import sys
import uuid
import json
import time
import hashlib
import shutil
import subprocess
from typing import Any, Dict, List, Tuple

SCHEMA_VERSION = "telemetry.v1"

def iso_ts() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime()) + f".{int((time.time()%1)*1000):03d}Z"

def ensure_dir(p: str) -> None:
    os.makedirs(p, exist_ok=True)

def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def write_json(path: str, obj: Any) -> None:
    ensure_dir(os.path.dirname(path))
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=2, sort_keys=True)

def append_jsonl(path: str, obj: Dict[str, Any]) -> None:
    ensure_dir(os.path.dirname(path))
    with open(path, "a", encoding="utf-8") as f:
        f.write(json.dumps(obj, sort_keys=True) + "\n")

def emit_event(run_dir: str, run_id: str, event: str, data: Dict[str, Any] | None = None) -> None:
    rec = {"ts": iso_ts(), "event": event, "run_id": run_id, "schema_version": SCHEMA_VERSION, "data": data or {}}
    append_jsonl(os.path.join(run_dir, "events.jsonl"), rec)

def run_cmd(cmd: List[str], cwd: str, timeout_sec: int) -> Tuple[int, str, float]:
    t0 = time.time()
    print(f"RUN: {' '.join(cmd)}", flush=True)
    p = subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=timeout_sec)
    dt = time.time() - t0
    return p.returncode, p.stdout, dt

def filter_comment_lines(text: str) -> str:
    lines = [ln for ln in text.splitlines() if ln.strip() and not ln.strip().startswith("#")]
    return "\n".join(lines)

def extract_section_lines(text: str, header: str) -> List[str]:
    lines = text.splitlines()
    start = None
    for i, ln in enumerate(lines):
        if ln.strip() == f"# {header}":
            start = i + 1
            break
    if start is None:
        raise RuntimeError(f"section not found: # {header}")
    out: List[str] = []
    for j in range(start, len(lines)):
        t = lines[j].strip()
        if t.startswith("# "):
            break
        if not t:
            continue
        if t.startswith("#"):
            continue
        out.append(lines[j])
    if not out:
        raise RuntimeError(f"section empty: {header}")
    return out

def write_manifest(run_dir: str, files: List[str]) -> None:
    items = []
    for p in files:
        items.append({
            "path": p.replace("\\\\", "/"),
            "bytes": os.path.getsize(p),
            "sha256": sha256_file(p),
        })
    write_json(os.path.join(run_dir, "manifest.json"), {"schema_version": SCHEMA_VERSION, "items": items})

def main() -> int:
    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
    print(f"repo_root={repo_root}", flush=True)

    lake = shutil.which("lake")
    if not lake:
        print("ERROR: 'lake' not found on PATH from Python. Run in the same shell where 'lake' works.", file=sys.stderr)
        return 2

    timeout_sec = int(os.environ.get("COHERENCE_RUN_TIMEOUT", "1800"))  # 30 min per command default

    run_id = uuid.uuid4().hex[:12]
    run_dir = os.path.join(repo_root, "paper", "out", "runs", run_id)
    artifacts_dir = os.path.join(run_dir, "artifacts")
    ensure_dir(artifacts_dir)

    print(f"run_id={run_id}", flush=True)
    print(f"run_dir={run_dir}", flush=True)

    emit_event(run_dir, run_id, "run.start", {
        "engine": "run_wrapper",
        "python": sys.version.split()[0],
        "platform": sys.platform,
    })

    LEAN_EVALS = {
        "tree_of_life_bands": os.path.join(repo_root, "CoherenceLattice", "Coherence", "TreeOfLifeBandCSV.lean"),
        "crop_circle_rotated_centers": os.path.join(repo_root, "CoherenceLattice", "Coherence", "CropCircleRotatedCentersEval.lean"),
        "music_profiles": os.path.join(repo_root, "CoherenceLattice", "Coherence", "MusicScaffoldEval.lean"),
    }

    # CSV artifacts only (for metrics.artifacts_count)
    csv_artifacts: List[str] = []
    # Everything we want hashed in the manifest (events included AFTER run.end)
    manifest_files: List[str] = []

    try:
        def eval_lean(step_id: str, lean_path: str) -> str:
            emit_event(run_dir, run_id, "step.start", {"step_id": step_id, "lean_path": lean_path})
            code, out, dt = run_cmd([lake, "env", "lean", lean_path], cwd=repo_root, timeout_sec=timeout_sec)
            emit_event(run_dir, run_id, "step.end", {"step_id": step_id, "status": "ok" if code == 0 else "error", "duration_sec": dt})
            if code != 0:
                raise RuntimeError(f"lean eval failed for {lean_path}\n{out}")
            return out

        # STEP 1
        print("STEP 1/3: TreeOfLifeBandCSV", flush=True)
        tol_out = eval_lean("tree_of_life_bands", LEAN_EVALS["tree_of_life_bands"])
        log1 = os.path.join(run_dir, "logs_tree_of_life_bands.json")
        write_json(log1, {"stdout": tol_out})
        manifest_files.append(log1)

        tol_csv = filter_comment_lines(tol_out)
        tol_path = os.path.join(artifacts_dir, "tree_of_life_bands.csv")
        with open(tol_path, "w", encoding="utf-8", newline="\n") as f:
            f.write(tol_csv + "\n")
        csv_artifacts.append(tol_path)
        manifest_files.append(tol_path)

        # STEP 2
        print("STEP 2/3: CropCircleRotatedCentersEval", flush=True)
        crop_out = eval_lean("crop_circle_rotated_centers", LEAN_EVALS["crop_circle_rotated_centers"])
        log2 = os.path.join(run_dir, "logs_crop_circle_rotated_centers.json")
        write_json(log2, {"stdout": crop_out})
        manifest_files.append(log2)

        crop_csv = filter_comment_lines(crop_out)
        crop_path = os.path.join(artifacts_dir, "crop_circle_rotated_centers.csv")
        with open(crop_path, "w", encoding="utf-8", newline="\n") as f:
            f.write(crop_csv + "\n")
        csv_artifacts.append(crop_path)
        manifest_files.append(crop_path)

        # STEP 3
        print("STEP 3/3: MusicScaffoldEval (profiles + split)", flush=True)
        music_out = eval_lean("music_profiles", LEAN_EVALS["music_profiles"])
        log3 = os.path.join(run_dir, "logs_music_profiles.json")
        write_json(log3, {"stdout": music_out})
        manifest_files.append(log3)

        combined_path = os.path.join(artifacts_dir, "music_scaffold_profiles.csv")
        with open(combined_path, "w", encoding="utf-8", newline="\n") as f:
            f.write(music_out)
            if not music_out.endswith("\n"):
                f.write("\n")
        csv_artifacts.append(combined_path)
        manifest_files.append(combined_path)

        scale_lines = extract_section_lines(music_out, "SCALE")
        maj_lines = extract_section_lines(music_out, "CHORDS_MAJOR")
        min_lines = extract_section_lines(music_out, "CHORDS_MINOR")

        scale_path = os.path.join(artifacts_dir, "music_scale.csv")
        maj_path = os.path.join(artifacts_dir, "music_chords_major.csv")
        min_path = os.path.join(artifacts_dir, "music_chords_minor.csv")

        for pth, lines in [(scale_path, scale_lines), (maj_path, maj_lines), (min_path, min_lines)]:
            with open(pth, "w", encoding="utf-8", newline="\n") as f:
                f.write("\n".join(lines) + "\n")
            csv_artifacts.append(pth)
            manifest_files.append(pth)

        # metrics.json (stable before run.end)
        metrics_path = os.path.join(run_dir, "metrics.json")
        write_json(metrics_path, {
            "schema_version": SCHEMA_VERSION,
            "run_id": run_id,
            "artifacts_count": len(csv_artifacts),
        })
        manifest_files.append(metrics_path)

        # Emit run.end BEFORE manifest (so events.jsonl is final when hashed)
        emit_event(run_dir, run_id, "run.end", {"status": "ok", "csv_artifacts_count": len(csv_artifacts)})

        # Now include events.jsonl in manifest (finalized)
        events_path = os.path.join(run_dir, "events.jsonl")
        manifest_files.append(events_path)

        # Manifest LAST write (no more file mutations after this)
        write_manifest(run_dir, manifest_files)

        print("DONE OK", flush=True)
        return 0

    except Exception as e:
        emit_event(run_dir, run_id, "run.end", {"status": "error", "error": str(e)})
        print(f"ERROR:\n{e}", file=sys.stderr)
        return 2

if __name__ == "__main__":
    raise SystemExit(main())