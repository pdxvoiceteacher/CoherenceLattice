from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from typing import Any, List

REQUIRED_FILES = ["events.jsonl", "metrics.json", "manifest.json"]
REQUIRED_EVENTS = {"run.start", "run.end"}

EXPECTED_ARTIFACTS = [
    "tree_of_life_bands.csv",
    "crop_circle_rotated_centers.csv",
    "music_scaffold_profiles.csv",
    "music_scale.csv",
    "music_chords_major.csv",
    "music_chords_minor.csv",
]

def die(msg: str, code: int = 2) -> None:
    print(f"VALIDATION FAILED: {msg}", file=sys.stderr)
    raise SystemExit(code)

def read_json(path: str) -> Any:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def resolve_manifest_path(run_dir: str, p: str) -> str:
    p2 = p.replace("/", os.sep)
    if os.path.isabs(p2) and os.path.exists(p2):
        return p2
    return os.path.join(run_dir, p2)

def read_first_line(path: str) -> str:
    with open(path, "r", encoding="utf-8", newline="") as f:
        return (f.readline() or "").strip()

def read_lines(path: str) -> List[str]:
    with open(path, "r", encoding="utf-8", newline="") as f:
        return [ln.rstrip("\n") for ln in f.readlines()]

def validate_events(run_dir: str) -> str:
    events_path = os.path.join(run_dir, "events.jsonl")
    run_ids = set()
    seen_events = set()

    with open(events_path, "r", encoding="utf-8") as f:
        for idx, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except Exception as e:
                die(f"events.jsonl line {idx} invalid JSON: {e}")
            for k in ["ts", "event", "run_id", "schema_version"]:
                if k not in rec:
                    die(f"events.jsonl line {idx} missing key: {k}")
            run_ids.add(str(rec["run_id"]))
            seen_events.add(str(rec["event"]))

    missing = REQUIRED_EVENTS - seen_events
    if missing:
        die(f"events.jsonl missing required events: {sorted(missing)}")

    if len(run_ids) != 1:
        die(f"events.jsonl contains multiple run_id values: {sorted(run_ids)}")

    return next(iter(run_ids))

def validate_metrics(run_dir: str, run_id: str) -> None:
    metrics_path = os.path.join(run_dir, "metrics.json")
    m = read_json(metrics_path)
    if "schema_version" not in m:
        die("metrics.json missing schema_version")
    if "run_id" not in m:
        die("metrics.json missing run_id")
    if str(m["run_id"]) != run_id:
        die(f"metrics.json run_id mismatch: {m['run_id']} != {run_id}")

    artifacts_dir = os.path.join(run_dir, "artifacts")
    csvs = [x for x in os.listdir(artifacts_dir) if x.lower().endswith(".csv")]
    if "artifacts_count" in m:
        ac = int(m["artifacts_count"])
        if ac != len(csvs):
            die(f"metrics.json artifacts_count={ac} but artifacts/*.csv count={len(csvs)}")

def validate_manifest(run_dir: str) -> None:
    man = read_json(os.path.join(run_dir, "manifest.json"))
    if "items" not in man or not isinstance(man["items"], list):
        die("manifest.json missing items list")

    for item in man["items"]:
        for k in ["path", "bytes", "sha256"]:
            if k not in item:
                die(f"manifest item missing key: {k}")

        p = resolve_manifest_path(run_dir, str(item["path"]))
        if not os.path.exists(p):
            die(f"manifest item path does not exist: {item['path']} -> {p}")

        size = os.path.getsize(p)
        if int(item["bytes"]) != int(size):
            die(f"manifest bytes mismatch for {p}: manifest={item['bytes']} actual={size}")

        h = sha256_file(p)
        if str(item["sha256"]).lower() != h.lower():
            die(f"manifest sha256 mismatch for {p}: manifest={item['sha256']} actual={h}")

def validate_artifacts(run_dir: str) -> None:
    artifacts_dir = os.path.join(run_dir, "artifacts")
    if not os.path.isdir(artifacts_dir):
        die("missing artifacts/ directory")

    missing = [p for p in EXPECTED_ARTIFACTS if not os.path.exists(os.path.join(artifacts_dir, p))]
    if missing:
        die(f"missing expected artifacts: {missing}")

    # headers
    if read_first_line(os.path.join(artifacts_dir, "tree_of_life_bands.csv")) != "name,E,T,psi,band":
        die("tree_of_life_bands.csv header mismatch")

    exp_crop = "theta,i,cx,cy,cxRot,cyRot,rBase,rRot,absDiff,absDiffToR,okAngle"
    if read_first_line(os.path.join(artifacts_dir, "crop_circle_rotated_centers.csv")) != exp_crop:
        die("crop_circle_rotated_centers.csv header mismatch")

    crop_lines = [ln for ln in read_lines(os.path.join(artifacts_dir, "crop_circle_rotated_centers.csv")) if ln.strip()]
    last = crop_lines[-1].split(",")
    if not last[0].strip().startswith("-1") or last[1].strip() != "-1":
        die("crop_circle_rotated_centers.csv missing global summary row (theta=-1,i=-1)")

    if read_first_line(os.path.join(artifacts_dir, "music_scale.csv")) != "name,ratio,freqHz":
        die("music_scale.csv header mismatch")

    exp_ch = "profile,chord,expectedOk,ok,match,ratios,freqsHz"
    if read_first_line(os.path.join(artifacts_dir, "music_chords_major.csv")) != exp_ch:
        die("music_chords_major.csv header mismatch")

    def summary_ok(path: str) -> None:
        lines = [ln for ln in read_lines(path) if ln.strip()]
        found = False
        for ln in lines[1:]:
            cols = ln.split(",")
            if len(cols) < 4:
                continue
            if cols[1].strip() == "__SUMMARY__":
                found = True
                if cols[3].strip().lower() != "true":
                    die(f"{os.path.basename(path)} __SUMMARY__ ok != true: {ln}")
        if not found:
            die(f"{os.path.basename(path)} missing __SUMMARY__ row")

    summary_ok(os.path.join(artifacts_dir, "music_chords_major.csv"))
    summary_ok(os.path.join(artifacts_dir, "music_chords_minor.csv"))

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("run_dir")
    args = ap.parse_args()
    run_dir = os.path.abspath(args.run_dir)
    if not os.path.isdir(run_dir):
        die(f"run_dir does not exist: {run_dir}")

    for f in REQUIRED_FILES:
        if not os.path.exists(os.path.join(run_dir, f)):
            die(f"missing required file: {f}")

    run_id = validate_events(run_dir)
    validate_metrics(run_dir, run_id)
    validate_artifacts(run_dir)
    validate_manifest(run_dir)

    print(f"VALIDATION OK run_id={run_id} run_dir={run_dir}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())