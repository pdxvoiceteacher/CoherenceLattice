from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from typing import Any, Dict, List

def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def read_json(path: str) -> Any:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def write_json(path: str, obj: Any) -> None:
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=2, sort_keys=True)

def resolve(run_dir: str, p: str) -> str:
    p2 = p.replace("/", os.sep)
    if os.path.isabs(p2) and os.path.exists(p2):
        return p2
    return os.path.join(run_dir, p2)

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("run_dir")
    args = ap.parse_args()

    run_dir = os.path.abspath(args.run_dir)
    man_path = os.path.join(run_dir, "manifest.json")
    if not os.path.exists(man_path):
        print("No manifest.json found.", file=sys.stderr)
        return 2

    man = read_json(man_path)
    items = man.get("items", [])
    if not isinstance(items, list):
        print("manifest.json missing items list.", file=sys.stderr)
        return 2

    fixed: List[Dict[str, Any]] = []
    for it in items:
        p = resolve(run_dir, str(it["path"]))
        if not os.path.exists(p):
            print(f"Skipping missing: {it['path']} -> {p}", file=sys.stderr)
            continue
        fixed.append({
            "path": it["path"],
            "bytes": os.path.getsize(p),
            "sha256": sha256_file(p),
        })

    man["items"] = fixed
    write_json(man_path, man)
    print(f"Repaired manifest: {man_path}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())