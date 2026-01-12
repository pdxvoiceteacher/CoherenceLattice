#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


@dataclass
class AppliedChange:
    op: str
    path: str
    changed: bool
    sha256_before: Optional[str] = None
    sha256_after: Optional[str] = None
    note: Optional[str] = None


def _read_text(p: Path) -> str:
    return p.read_text(encoding="utf-8-sig")


def _write_text(p: Path, s: str) -> None:
    # Force LF and UTF-8 for determinism
    p.write_text(s.replace("\r\n", "\n").replace("\r", "\n"), encoding="utf-8", newline="\n")


def _sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def _sha256_file(p: Path) -> str:
    return _sha256_bytes(p.read_bytes())


def _resolve_target_path(workdir: Path, raw_path: str) -> Path:
    rp = Path(raw_path)
    if rp.is_absolute():
        return rp
    return workdir / rp


def _parse_json_path(json_path: str) -> List[str]:
    """
    Supports either:
      - JSON Pointer: "/a/b/0"
      - Dot path: "a.b.0"
    """
    jp = json_path.strip()
    if jp.startswith("/"):
        # JSON Pointer
        parts = []
        for seg in jp.split("/")[1:]:
            seg = seg.replace("~1", "/").replace("~0", "~")
            parts.append(seg)
        return parts
    # Dot path
    return [p for p in jp.split(".") if p != ""]


def _json_set(doc: Any, path_parts: List[str], value: Any) -> Tuple[Any, bool]:
    """
    Set value at path_parts. Creates dict containers as needed.
    If a path part is an integer index, uses list indexing.
    Returns (doc, changed).
    """
    cur = doc
    for i, part in enumerate(path_parts):
        is_last = i == len(path_parts) - 1

        # list index?
        idx = None
        if re.fullmatch(r"\d+", part):
            idx = int(part)

        if is_last:
            if idx is not None:
                if not isinstance(cur, list):
                    raise TypeError(f"Expected list at {path_parts[:i]} but found {type(cur).__name__}")
                # expand list if needed
                while len(cur) <= idx:
                    cur.append(None)
                changed = cur[idx] != value
                cur[idx] = value
                return doc, changed
            else:
                if not isinstance(cur, dict):
                    raise TypeError(f"Expected dict at {path_parts[:i]} but found {type(cur).__name__}")
                changed = cur.get(part) != value
                cur[part] = value
                return doc, changed

        # not last
        if idx is not None:
            if not isinstance(cur, list):
                raise TypeError(f"Expected list at {path_parts[:i]} but found {type(cur).__name__}")
            while len(cur) <= idx:
                cur.append({})
            nxt = cur[idx]
            if nxt is None:
                nxt = {}
                cur[idx] = nxt
            cur = nxt
        else:
            if not isinstance(cur, dict):
                raise TypeError(f"Expected dict at {path_parts[:i]} but found {type(cur).__name__}")
            if part not in cur or cur[part] is None:
                cur[part] = {}
            cur = cur[part]

    return doc, False


def apply_proposal(proposal: Dict[str, Any], workdir: Path) -> List[AppliedChange]:
    recs = proposal.get("recommendations") or []
    applied: List[AppliedChange] = []

    for r in recs:
        a = r.get("action_v2")
        if not a:
            continue

        op = a.get("op")
        raw_path = a.get("path")
        if not op or not raw_path:
            continue

        target = _resolve_target_path(workdir, raw_path)

        if not target.exists():
            applied.append(AppliedChange(op=op, path=str(target), changed=False, note="target missing"))
            continue

        sha_before = _sha256_file(target)

        if op == "json_set":
            json_path = a.get("json_path")
            value = a.get("value")
            if not json_path:
                applied.append(AppliedChange(op=op, path=str(target), changed=False, sha256_before=sha_before, note="missing json_path"))
                continue

            doc = json.loads(_read_text(target))
            parts = _parse_json_path(str(json_path))
            doc2, changed = _json_set(doc, parts, value)
            if changed:
                # Deterministic JSON output
                out = json.dumps(doc2, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
                _write_text(target, out)

            sha_after = _sha256_file(target)
            applied.append(AppliedChange(op=op, path=str(target), changed=changed, sha256_before=sha_before, sha256_after=sha_after))

        elif op == "text_replace":
            pattern = a.get("pattern")
            replacement = a.get("replacement")
            max_repl = a.get("max_replacements")
            if pattern is None or replacement is None:
                applied.append(AppliedChange(op=op, path=str(target), changed=False, sha256_before=sha_before, note="missing pattern/replacement"))
                continue

            text = _read_text(target)
            count = 0 if max_repl is None else int(max_repl)
            new_text, n = re.subn(pattern, replacement, text, count=count, flags=re.MULTILINE)
            changed = n > 0
            if changed:
                _write_text(target, new_text)

            sha_after = _sha256_file(target)
            applied.append(AppliedChange(op=op, path=str(target), changed=changed, sha256_before=sha_before, sha256_after=sha_after,
                                        note=f"replacements={n}"))

        else:
            applied.append(AppliedChange(op=op, path=str(target), changed=False, sha256_before=sha_before, note="unsupported op"))

    return applied


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--proposal", required=True, help="Path to plasticity tuning proposal JSON")
    ap.add_argument("--workdir", default=".", help="Repo/workdir root where file paths are resolved")
    ap.add_argument("--out-manifest", default="", help="Write applied-changes manifest JSON here")
    args = ap.parse_args()

    proposal_path = Path(args.proposal)
    workdir = Path(args.workdir).resolve()

    proposal = json.loads(proposal_path.read_text(encoding="utf-8"))
    applied = apply_proposal(proposal, workdir)

    changed_files = [a for a in applied if a.changed]
    print(f"[apply_tuning_proposal] actions_seen={len(applied)} changed_files={len(changed_files)} workdir={workdir}")

    if args.out_manifest:
        out = {
            "schema": "applied_tuning_manifest_v1",
            "proposal": str(proposal_path),
            "workdir": str(workdir),
            "actions_seen": len(applied),
            "changed_files": len(changed_files),
            "applied": [a.__dict__ for a in applied],
        }
        Path(args.out_manifest).parent.mkdir(parents=True, exist_ok=True)
        Path(args.out_manifest).write_text(json.dumps(out, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n")
        print(f"[apply_tuning_proposal] wrote manifest: {args.out_manifest}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
