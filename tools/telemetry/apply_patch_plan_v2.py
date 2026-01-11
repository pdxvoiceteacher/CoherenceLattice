from __future__ import annotations

import argparse
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Tuple, Optional

from jsonschema import Draft202012Validator


ALLOW_PREFIXES = ["config/plasticity/", "governance/", "schema/"]
DENY_PREFIXES = [".github/", "tools/", "ucc/", "python/", "config/"]  # config/* except config/plasticity/
BUDGET_KEYS = [
    "perturb", "retry", "timeout", "concurrency", "parallel", "workers", "matrix",
    "interval", "freq", "schedule", "max_", "attempt", "budget"
]


def _now_utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _hash_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def _hash_file(p: Path) -> str:
    return _hash_bytes(p.read_bytes())


def _canonical_write_json(p: Path, obj: Any) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8", newline="\n")


def _read_json(p: Path) -> Any:
    return json.loads(p.read_text(encoding="utf-8"))


def _is_allowed_path(rel: str) -> Tuple[bool, str]:
    rel2 = rel.replace("\\", "/")
    if rel2.startswith("/"):
        return False, "absolute paths are disallowed"
    if ".." in Path(rel2).parts:
        return False, "path traversal is disallowed"
    if not any(rel2.startswith(a) for a in ALLOW_PREFIXES):
        return False, f"path not allowlisted: {rel2}"
    for d in DENY_PREFIXES:
        if rel2.startswith(d) and not rel2.startswith("config/plasticity/"):
            return False, f"path denied by prefix: {d}"
    return True, ""


def _json_get(root: Any, path: str) -> Any:
    cur = root
    if path.startswith("/"):
        parts = [p for p in path.split("/") if p]
    else:
        parts = [p for p in path.split(".") if p]
    for part in parts:
        if isinstance(cur, list):
            cur = cur[int(part)]
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
    lp = (json_path or "").lower()
    return any(k in lp for k in BUDGET_KEYS)


def apply_patch_plan(
    plan_path: Path,
    repo_root: Path,
    *,
    dry_run: bool = False,
    receipt_out: Optional[Path] = None,
    rollback_out: Optional[Path] = None,
    backup_dir: Optional[Path] = None,
) -> Dict[str, Any]:
    plan_schema = _read_json(Path("schema/plasticity_patch_plan_v2.schema.json"))
    plan = _read_json(plan_path)
    Draft202012Validator(plan_schema).validate(plan)

    proposal_id = plan.get("proposal_id", "unknown")
    created_at = _now_utc_iso()

    allow_ok = True
    budget_ok = True
    notes: List[str] = []

    file_changes: List[Dict[str, Any]] = []
    rollback_ops: List[Dict[str, Any]] = []

    # default backup dir if requested
    if backup_dir is None and rollback_out is not None:
        backup_dir = Path("governance/proposals/rollbacks") / proposal_id / "backups"

    for op_index, op in enumerate(plan.get("operations", [])):
        rel = (op.get("path") or "").replace("\\", "/")
        ok, why = _is_allowed_path(rel)
        if not ok:
            allow_ok = False
            notes.append(f"DENY path {rel}: {why}")
            file_changes.append({
                "op_index": op_index, "op": op.get("op"), "path": rel,
                "ok": False, "before_hash": "", "after_hash": "",
                "details": {"deny": why}
            })
            continue

        target = (repo_root / rel).resolve()
        if not str(target).startswith(str(repo_root.resolve())):
            allow_ok = False
            notes.append(f"DENY escape path: {rel}")
            file_changes.append({
                "op_index": op_index, "op": op.get("op"), "path": rel,
                "ok": False, "before_hash": "", "after_hash": "",
                "details": {"deny": "escape_path"}
            })
            continue

        if not target.exists():
            allow_ok = False
            notes.append(f"DENY missing file: {rel}")
            file_changes.append({
                "op_index": op_index, "op": op.get("op"), "path": rel,
                "ok": False, "before_hash": "", "after_hash": "",
                "details": {"deny": "missing_file"}
            })
            continue

        if target.stat().st_size > 1_000_000:
            allow_ok = False
            notes.append(f"DENY file too large (>1MB): {rel}")
            file_changes.append({
                "op_index": op_index, "op": op.get("op"), "path": rel,
                "ok": False, "before_hash": "", "after_hash": "",
                "details": {"deny": "file_too_large"}
            })
            continue

        before_hash = _hash_file(target)
        after_hash = before_hash
        op_ok = True
        details: Dict[str, Any] = {}

        if op.get("op") == "json_set":
            if not rel.endswith(".json"):
                allow_ok = False
                op_ok = False
                notes.append(f"DENY json_set requires .json: {rel}")
                details["deny"] = "json_set_requires_json"
            else:
                json_path = op.get("json_path") or ""
                if not json_path:
                    allow_ok = False
                    op_ok = False
                    details["deny"] = "missing_json_path"
                    notes.append(f"DENY json_set missing json_path: {rel}")
                else:
                    doc = _read_json(target)
                    try:
                        old_val = _json_get(doc, json_path)
                    except Exception:
                        old_val = None

                    new_val = op.get("value")

                    # Budget invariant: do not introduce or increase "budget-ish" keys
                    if _budget_key_hit(json_path):
                        if old_val is None:
                            budget_ok = False
                            op_ok = False
                            details["deny"] = "budget_key_introduction"
                            notes.append(f"DENY budget key introduction at {rel}:{json_path}")
                        else:
                            try:
                                old_num = float(old_val)
                                new_num = float(new_val)
                                if new_num > old_num:
                                    budget_ok = False
                                    op_ok = False
                                    details["deny"] = "budget_increase"
                                    notes.append(f"DENY budget increase at {rel}:{json_path} {old_num} -> {new_num}")
                            except Exception:
                                if old_val in (False, "false", "False") and new_val in (True, "true", "True"):
                                    budget_ok = False
                                    op_ok = False
                                    details["deny"] = "budget_enable"
                                    notes.append(f"DENY budget enable at {rel}:{json_path} {old_val} -> {new_val}")

                    details.update({"json_path": json_path, "old_value": old_val, "new_value": new_val})

                    if op_ok and (not dry_run):
                        _json_set(doc, json_path, new_val)
                        _canonical_write_json(target, doc)
                        after_hash = _hash_file(target)

                    # Rollback op: restore old value
                    if rollback_out is not None and old_val is not None:
                        rollback_ops.append({
                            "op": "json_set",
                            "path": rel,
                            "json_path": json_path,
                            "value": old_val,
                            "backup_path": None,
                            "note": f"rollback op_index={op_index}"
                        })

        elif op.get("op") == "text_replace":
            pattern = op.get("pattern") or ""
            repl = op.get("replacement") or ""
            if not pattern:
                allow_ok = False
                op_ok = False
                details["deny"] = "missing_pattern"
                notes.append(f"DENY text_replace missing pattern: {rel}")
            else:
                if not (rel.endswith(".md") or rel.endswith(".txt") or rel.endswith(".json") or rel.endswith(".yml") or rel.endswith(".yaml")):
                    allow_ok = False
                    op_ok = False
                    details["deny"] = "bad_file_type"
                    notes.append(f"DENY text_replace file type: {rel}")
                else:
                    max_repl = op.get("max_replacements")
                    txt = target.read_text(encoding="utf-8")
                    rx = re.compile(pattern, flags=re.MULTILINE)
                    if max_repl is None:
                        new_txt, n = rx.subn(repl, txt)
                    else:
                        new_txt, n = rx.subn(repl, txt, count=int(max_repl))
                    details.update({"replacements": int(n)})

                    # Conservative thermo rule: do not allow numeric text_replace inside config/plasticity/*
                    if rel.startswith("config/plasticity/") and re.search(r"\d", repl):
                        budget_ok = False
                        op_ok = False
                        details["deny"] = "numeric_text_replace_in_config"
                        notes.append(f"DENY numeric text_replace in config/plasticity: {rel}")

                    backup_rel = None
                    if rollback_out is not None and backup_dir is not None:
                        # Write backup of original file for rollback
                        backup_dir.mkdir(parents=True, exist_ok=True)
                        safe_name = rel.replace("/", "__")
                        backup_file = backup_dir / f"{safe_name}.bak"
                        backup_file.write_text(txt, encoding="utf-8", newline="\n")
                        backup_rel = str(backup_file).replace("\\", "/")
                        rollback_ops.append({
                            "op": "restore_file",
                            "path": rel,
                            "json_path": None,
                            "value": None,
                            "backup_path": backup_rel,
                            "note": f"rollback op_index={op_index}"
                        })

                    if op_ok and (not dry_run):
                        target.write_text(new_txt, encoding="utf-8", newline="\n")
                        after_hash = _hash_file(target)

                    details["backup_path"] = backup_rel

        else:
            allow_ok = False
            op_ok = False
            details["deny"] = "unsupported_op"
            notes.append(f"DENY unsupported op: {op.get('op')}")

        file_changes.append({
            "op_index": op_index,
            "op": op.get("op"),
            "path": rel,
            "ok": bool(op_ok),
            "before_hash": before_hash,
            "after_hash": after_hash,
            "details": details or None
        })

    # Emit rollback plan (if requested)
    rollback_path_str: Optional[str] = None
    if rollback_out is not None:
        rollback_plan = {
            "schema": "plasticity_rollback_plan_v2_1",
            "proposal_id": proposal_id,
            "created_at_utc": created_at,
            "patch_plan_path": str(plan_path).replace("\\", "/"),
            "operations": rollback_ops
        }
        _canonical_write_json(rollback_out, rollback_plan)
        rollback_path_str = str(rollback_out).replace("\\", "/")

    # Emit receipt (if requested)
    if receipt_out is not None:
        receipt = {
            "schema": "plasticity_receipt_v2_1",
            "proposal_id": proposal_id,
            "created_at_utc": created_at,
            "patch_plan_path": str(plan_path).replace("\\", "/"),
            "dry_run": bool(dry_run),
            "thermo": {"allowlist_ok": bool(allow_ok), "budget_ok": bool(budget_ok), "notes": notes},
            "file_changes": file_changes,
            "rollback_plan_path": rollback_path_str
        }
        _canonical_write_json(receipt_out, receipt)

    return {"allowlist_ok": allow_ok, "budget_ok": budget_ok, "notes": notes, "rollback_plan_path": rollback_path_str, "receipt_path": str(receipt_out).replace("\\","/") if receipt_out else None}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--patch-plan", required=True)
    ap.add_argument("--repo-root", default=".")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--receipt-out", default="", help="If set, write receipt JSON here")
    ap.add_argument("--rollback-out", default="", help="If set, write rollback plan JSON here")
    ap.add_argument("--backup-dir", default="", help="If set, store backups here (used for restore_file rollback ops)")
    args = ap.parse_args()

    receipt_out = Path(args.receipt_out) if args.receipt_out.strip() else None
    rollback_out = Path(args.rollback_out) if args.rollback_out.strip() else None
    backup_dir = Path(args.backup_dir) if args.backup_dir.strip() else None

    res = apply_patch_plan(Path(args.patch_plan), Path(args.repo_root), dry_run=args.dry_run, receipt_out=receipt_out, rollback_out=rollback_out, backup_dir=backup_dir)
    print(json.dumps(res, ensure_ascii=False, sort_keys=True, indent=2))
    if not (res["allowlist_ok"] and res["budget_ok"]):
        raise SystemExit(2)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
