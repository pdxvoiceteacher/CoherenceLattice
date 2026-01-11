from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any, Dict, List, Tuple

from jsonschema import Draft202012Validator


ALLOW_PREFIXES = ["config/plasticity/", "governance/", "schema/"]
DENY_PREFIXES = [".github/", "tools/", "ucc/", "python/", "config/"]  # config/* except config/plasticity/
BUDGET_KEYS = [
    "perturb", "retry", "timeout", "concurrency", "parallel", "workers", "matrix",
    "interval", "freq", "schedule", "max_", "attempt", "budget"
]


def _canonical_write_json(p: Path, obj: Any) -> None:
    p.write_text(json.dumps(obj, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n")


def _read_json(p: Path) -> Any:
    return json.loads(p.read_text(encoding="utf-8"))


def _safe_rel(p: Path, root: Path) -> str:
    try:
        return str(p.relative_to(root)).replace("\\", "/")
    except Exception:
        return str(p.resolve()).replace("\\", "/")


def _is_allowed_path(rel: str) -> Tuple[bool, str]:
    rel2 = rel.replace("\\", "/")
    if rel2.startswith("/"):
        return False, "absolute paths are disallowed"
    if ".." in Path(rel2).parts:
        return False, "path traversal is disallowed"
    if not any(rel2.startswith(a) for a in ALLOW_PREFIXES):
        return False, f"path not allowlisted: {rel2}"
    # deny prefixes, except allowlisted config/plasticity/
    for d in DENY_PREFIXES:
        if rel2.startswith(d) and not rel2.startswith("config/plasticity/"):
            return False, f"path denied by prefix: {d}"
    return True, ""


def _json_get(root: Any, path: str) -> Any:
    cur = root
    if path.startswith("/"):  # JSON pointer-ish
        parts = [p for p in path.split("/") if p]
    else:
        parts = [p for p in path.split(".") if p]
    for part in parts:
        if isinstance(cur, list):
            idx = int(part)
            cur = cur[idx]
        elif isinstance(cur, dict):
            cur = cur[part]
        else:
            raise KeyError(f"Cannot traverse {part} in non-container")
    return cur


def _json_set(root: Any, path: str, value: Any) -> Tuple[Any, Any]:
    cur = root
    if path.startswith("/"):
        parts = [p for p in path.split("/") if p]
    else:
        parts = [p for p in path.split(".") if p]
    if not parts:
        raise ValueError("json_path is empty")
    for part in parts[:-1]:
        if isinstance(cur, list):
            cur = cur[int(part)]
        else:
            cur = cur.setdefault(part, {})
    last = parts[-1]
    old = None
    if isinstance(cur, list):
        i = int(last)
        old = cur[i]
        cur[i] = value
    else:
        old = cur.get(last)
        cur[last] = value
    return old, root


def _budget_key_hit(json_path: str) -> bool:
    lp = json_path.lower()
    return any(k in lp for k in BUDGET_KEYS)


def apply_patch_plan(plan_path: Path, repo_root: Path, *, dry_run: bool = False) -> Dict[str, Any]:
    schema = json.loads(Path("schema/plasticity_patch_plan_v2.schema.json").read_text(encoding="utf-8"))
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    Draft202012Validator(schema).validate(plan)

    allow_ok = True
    budget_ok = True
    thermo_notes: List[str] = []

    for op in plan["operations"]:
        rel = op["path"].replace("\\", "/")
        ok, why = _is_allowed_path(rel)
        if not ok:
            allow_ok = False
            thermo_notes.append(f"DENY path {rel}: {why}")
            continue

        target = (repo_root / rel).resolve()
        if not str(target).startswith(str(repo_root.resolve())):
            allow_ok = False
            thermo_notes.append(f"DENY escape path: {rel}")
            continue

        if not target.exists():
            allow_ok = False
            thermo_notes.append(f"DENY missing file: {rel}")
            continue

        # size guard (thermo safety / avoid huge churn)
        if target.stat().st_size > 1_000_000:
            allow_ok = False
            thermo_notes.append(f"DENY file too large (>1MB): {rel}")
            continue

        if op["op"] == "json_set":
            if not rel.endswith(".json"):
                allow_ok = False
                thermo_notes.append(f"DENY json_set requires .json: {rel}")
                continue

            json_path = op.get("json_path") or ""
            if not json_path:
                allow_ok = False
                thermo_notes.append(f"DENY json_set missing json_path: {rel}")
                continue

            doc = _read_json(target)
            try:
                old_val = _json_get(doc, json_path)
            except Exception:
                old_val = None

            new_val = op.get("value")

            # Budget invariant: if key smells like budget, do not allow increases or introductions
            if _budget_key_hit(json_path):
                if old_val is None:
                    budget_ok = False
                    thermo_notes.append(f"DENY budget key introduction at {rel}:{json_path}")
                    continue
                try:
                    old_num = float(old_val)
                    new_num = float(new_val)
                    if new_num > old_num:
                        budget_ok = False
                        thermo_notes.append(f"DENY budget increase at {rel}:{json_path} {old_num} -> {new_num}")
                        continue
                except Exception:
                    # For non-numeric, forbid enabling new capacity
                    if old_val in (False, "false", "False") and new_val in (True, "true", "True"):
                        budget_ok = False
                        thermo_notes.append(f"DENY budget enable at {rel}:{json_path} {old_val} -> {new_val}")
                        continue

            if not dry_run:
                _json_set(doc, json_path, new_val)
                _canonical_write_json(target, doc)

        elif op["op"] == "text_replace":
            pattern = op.get("pattern") or ""
            repl = op.get("replacement") or ""
            if not pattern:
                allow_ok = False
                thermo_notes.append(f"DENY text_replace missing pattern: {rel}")
                continue

            # restrict to text-like files in allowlist; allow .json too
            if not (rel.endswith(".md") or rel.endswith(".txt") or rel.endswith(".json") or rel.endswith(".yml") or rel.endswith(".yaml")):
                allow_ok = False
                thermo_notes.append(f"DENY text_replace file type: {rel}")
                continue

            max_repl = op.get("max_replacements")
            txt = target.read_text(encoding="utf-8")
            rx = re.compile(pattern, flags=re.MULTILINE)
            if max_repl is None:
                new_txt, n = rx.subn(repl, txt)
            else:
                new_txt, n = rx.subn(repl, txt, count=int(max_repl))

            # Budget invariant heuristic: if editing tuning config and replacement raises numeric values, deny
            if rel.startswith("config/plasticity/") and re.search(r"\d", repl):
                # conservative: do not allow text_replace to change numbers in config/plasticity/*
                budget_ok = False
                thermo_notes.append(f"DENY numeric text_replace in config/plasticity: {rel}")
                continue

            if not dry_run:
                target.write_text(new_txt, encoding="utf-8", newline="\n")

        else:
            allow_ok = False
            thermo_notes.append(f"DENY unsupported op: {op['op']}")

    return {"allowlist_ok": allow_ok, "budget_ok": budget_ok, "notes": thermo_notes}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--patch-plan", required=True)
    ap.add_argument("--repo-root", default=".")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    res = apply_patch_plan(Path(args.patch_plan), Path(args.repo_root), dry_run=args.dry_run)
    print(json.dumps(res, ensure_ascii=False, sort_keys=True, indent=2))
    # fail-closed if allowlist/budget not ok
    if not (res["allowlist_ok"] and res["budget_ok"]):
        raise SystemExit(2)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
