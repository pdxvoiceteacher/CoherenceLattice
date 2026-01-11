from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from jsonschema import Draft202012Validator

ALLOW_PREFIXES = ["config/plasticity/", "governance/", "schema/"]
DENY_PREFIXES = [".github/", "tools/", "ucc/", "python/", "config/"]


def _hash_bytes(b: bytes) -> str:
    import hashlib as _h
    return _h.sha256(b).hexdigest()


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
        return False, "absolute paths disallowed"
    if ".." in Path(rel2).parts:
        return False, "path traversal disallowed"
    if not any(rel2.startswith(a) for a in ALLOW_PREFIXES):
        return False, f"not allowlisted: {rel2}"
    for d in DENY_PREFIXES:
        if rel2.startswith(d) and not rel2.startswith("config/plasticity/"):
            return False, f"denied by prefix: {d}"
    return True, ""


def _json_set(doc: Any, path: str, value: Any) -> Any:
    cur = doc
    if path.startswith("/"):
        parts = [p for p in path.split("/") if p]
    else:
        parts = [p for p in path.split(".") if p]
    if not parts:
        raise ValueError("empty json_path")
    for part in parts[:-1]:
        if isinstance(cur, list):
            cur = cur[int(part)]
        else:
            cur = cur.setdefault(part, {})
    last = parts[-1]
    if isinstance(cur, list):
        cur[int(last)] = value
    else:
        cur[last] = value
    return doc


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rollback-plan", required=True)
    ap.add_argument("--repo-root", default=".")
    ap.add_argument("--apply", action="store_true", help="Actually apply rollback (default is dry-run)")
    ap.add_argument("--receipt-out", default="", help="Optional rollback receipt JSON path")
    args = ap.parse_args()

    rb_path = Path(args.rollback_plan)
    repo_root = Path(args.repo_root).resolve()
    schema = _read_json(Path("schema/plasticity_rollback_plan_v2_1.schema.json"))
    rb = _read_json(rb_path)
    Draft202012Validator(schema).validate(rb)

    changes: List[Dict[str, Any]] = []
    ok_all = True

    for i, op in enumerate(rb.get("operations", [])):
        rel = str(op.get("path","")).replace("\\","/")
        ok, why = _is_allowed_path(rel)
        if not ok:
            ok_all = False
            changes.append({"op_index": i, "ok": False, "path": rel, "reason": why})
            continue

        target = (repo_root / rel).resolve()
        if not str(target).startswith(str(repo_root)):
            ok_all = False
            changes.append({"op_index": i, "ok": False, "path": rel, "reason": "escape_path"})
            continue

        if not target.exists():
            ok_all = False
            changes.append({"op_index": i, "ok": False, "path": rel, "reason": "missing_target"})
            continue

        before = _hash_file(target)
        after = before

        op_type = op.get("op")
        if op_type == "json_set":
            json_path = op.get("json_path")
            value = op.get("value")
            if not (rel.endswith(".json") and isinstance(json_path, str) and json_path):
                ok_all = False
                changes.append({"op_index": i, "ok": False, "path": rel, "reason": "bad_json_set"})
                continue
            doc = _read_json(target)
            doc = _json_set(doc, json_path, value)
            if args.apply:
                _canonical_write_json(target, doc)
                after = _hash_file(target)

        elif op_type == "restore_file":
            backup_path = op.get("backup_path")
            if not backup_path:
                ok_all = False
                changes.append({"op_index": i, "ok": False, "path": rel, "reason": "missing_backup_path"})
                continue
            bp = Path(str(backup_path)).resolve()
            # Safety: backups must be inside repo_root
            if not str(bp).startswith(str(repo_root)):
                ok_all = False
                changes.append({"op_index": i, "ok": False, "path": rel, "reason": "backup_outside_repo"})
                continue
            if not bp.exists():
                ok_all = False
                changes.append({"op_index": i, "ok": False, "path": rel, "reason": "missing_backup_file"})
                continue
            if args.apply:
                target.write_text(bp.read_text(encoding="utf-8"), encoding="utf-8", newline="\n")
                after = _hash_file(target)
        else:
            ok_all = False
            changes.append({"op_index": i, "ok": False, "path": rel, "reason": f"unsupported_op:{op_type}"})
            continue

        changes.append({"op_index": i, "ok": True, "path": rel, "before_hash": before, "after_hash": after, "op": op_type})

    receipt = {
        "schema": "plasticity_rollback_receipt_v2_1",
        "rollback_plan_path": str(rb_path).replace("\\","/"),
        "ok": bool(ok_all),
        "applied": bool(args.apply),
        "changes": changes
    }

    if args.receipt_out.strip():
        _canonical_write_json(Path(args.receipt_out), receipt)

    print(json.dumps(receipt, ensure_ascii=False, sort_keys=True, indent=2))
    return 0 if ok_all else 2


if __name__ == "__main__":
    raise SystemExit(main())
