#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Optional


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def resolve_artifact(raw: str, run_dir: Path, repo_root: Path) -> Optional[Path]:
    """
    Cross-platform resolver.

    Artifacts may be:
      - absolute
      - repo-root relative (preferred)
      - run-dir relative
      - repo-root relative but redundantly prefixed by run_dir path
    """
    raw = str(raw)

    # Candidate raw spellings to try (keep POSIX slashes on Linux/macOS)
    cands = []
    cands.append(raw)
    cands.append(raw.replace("\\", "/"))

    # On Windows, also try backslash form
    try:
        import os
        if os.name == "nt":
            cands.append(raw.replace("/", "\\"))
    except Exception:
        pass

    def try_path(p: Path) -> Optional[Path]:
        if p.is_absolute() and p.exists():
            return p
        rp = repo_root / p
        if rp.exists():
            return rp
        rr = run_dir / p
        if rr.exists():
            return rr
        return None

    for s in cands:
        p = Path(s)
        hit = try_path(p)
        if hit:
            return hit

    # If raw includes run_dir prefix, strip it and try again
    try:
        run_rel = run_dir.relative_to(repo_root).as_posix()
        for s in cands:
            s2 = s.replace("\\", "/")
            if s2.startswith(run_rel + "/"):
                tail = s2[len(run_rel) + 1 :]
                hit = try_path(Path(tail))
                if hit:
                    return hit
    except Exception:
        pass

    return None


def infer_repo_root(start: Path) -> Path:
    cur = start.resolve()
    while cur != cur.parent:
        if (cur / ".git").exists():
            return cur
        cur = cur.parent
    return start.resolve()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("telemetry_json", help="Path to telemetry.json")
    ap.add_argument("--repo-root", default="", help="Repo root (default: inferred by walking up to .git)")
    args = ap.parse_args()

    tele = Path(args.telemetry_json).resolve()
    run_dir = tele.parent

    if args.repo_root:
        repo_root = Path(args.repo_root).resolve()
    else:
        repo_root = infer_repo_root(run_dir)

    doc = json.loads(tele.read_text(encoding="utf-8-sig"))

    if not doc.get("flags", {}).get("telemetry_ok", False):
        print("[verify_artifacts] FAIL telemetry_ok is false")
        return 2

    artifacts = doc.get("artifacts") or []
    if not artifacts:
        print("[verify_artifacts] FAIL no artifacts listed")
        return 2

    failed = False
    for a in artifacts:
        raw = str(a.get("path", ""))
        expected = str(a.get("sha256", "")).lower()

        resolved = resolve_artifact(raw, run_dir, repo_root)
        if not resolved:
            print(f"[verify_artifacts] FAIL missing artifact: raw={raw}")
            failed = True
            continue

        actual = sha256_file(resolved).lower()
        if actual != expected:
            print(f"[verify_artifacts] FAIL sha256 mismatch: raw={raw}")
            print(f"  expected={expected}")
            print(f"    actual={actual}")
            failed = True

    if failed:
        return 2

    print("[verify_artifacts] OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())



