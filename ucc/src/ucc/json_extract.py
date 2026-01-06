from __future__ import annotations

import csv
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union


# -------------------------------
# Helpers
# -------------------------------

class _Missing:
    pass


MISSING = _Missing()


def _repo_root() -> Path:
    # .../CoherenceLattice/ucc/src/ucc/json_extract.py -> parents[3] is repo root
    return Path(__file__).resolve().parents[3]


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _resolve_path(p: str) -> Path:
    pp = Path(str(p))
    if pp.is_absolute():
        return pp
    # Interpret as repo-root-relative (so "ucc/tasks/..." works)
    return (_repo_root() / pp).resolve()


def _parse_path(expr: str) -> List[Union[str, int]]:
    """
    Parse dotted path with optional list indices.

    Examples:
      metrics.delta_mean_Ppump        -> ["metrics","delta_mean_Ppump"]
      nested.arr[1].x                 -> ["nested","arr",1,"x"]
      a.b[0][2].c                     -> ["a","b",0,2,"c"]
    """
    s = str(expr).strip()
    if not s:
        raise ValueError("empty path")

    parts: List[Union[str, int]] = []
    buf: List[str] = []
    i = 0
    n = len(s)

    def flush_key() -> None:
        nonlocal buf
        if buf:
            k = "".join(buf).strip()
            if k:
                parts.append(k)
            buf = []

    while i < n:
        ch = s[i]
        if ch == ".":
            flush_key()
            i += 1
            continue
        if ch == "[":
            flush_key()
            j = s.find("]", i + 1)
            if j == -1:
                raise ValueError(f"unclosed '[' in path: {s}")
            idx_raw = s[i + 1 : j].strip()
            if not idx_raw.isdigit():
                raise ValueError(f"non-integer index [{idx_raw}] in path: {s}")
            parts.append(int(idx_raw))
            i = j + 1
            continue
        buf.append(ch)
        i += 1

    flush_key()
    return parts


def _get_by_parts(obj: Any, parts: List[Union[str, int]]) -> Any:
    cur = obj
    for p in parts:
        if isinstance(p, int):
            if not isinstance(cur, list):
                return MISSING
            if p < 0 or p >= len(cur):
                return MISSING
            cur = cur[p]
        else:
            if not isinstance(cur, dict):
                return MISSING
            if p not in cur:
                return MISSING
            cur = cur[p]
    return cur


def _coerce_type(val: Any, typ: str) -> Tuple[bool, Any, str]:
    """
    Returns (ok, coerced_value, reason_if_bad)
    """
    t = str(typ).strip().lower()

    if t in {"any", "raw"}:
        return True, val, ""

    if t in {"bool", "boolean"}:
        if isinstance(val, bool):
            return True, val, ""
        return False, None, f"expected bool, got {type(val).__name__}"

    if t in {"int", "integer"}:
        # bool is a subclass of int in Python; reject it explicitly
        if isinstance(val, bool):
            return False, None, "expected int, got bool"
        if isinstance(val, int):
            return True, val, ""
        if isinstance(val, float) and val.is_integer():
            return True, int(val), ""
        return False, None, f"expected int, got {type(val).__name__}"

    if t in {"number", "float", "real"}:
        if isinstance(val, bool):
            return False, None, "expected number, got bool"
        if isinstance(val, (int, float)):
            return True, val, ""
        return False, None, f"expected number, got {type(val).__name__}"

    if t in {"str", "string", "text"}:
        if isinstance(val, str):
            return True, val, ""
        return False, None, f"expected string, got {type(val).__name__}"

    return False, None, f"unknown type '{typ}'"


# -------------------------------
# UCC step
# -------------------------------

def extract_json_fields_task(
    task_doc: Dict[str, Any],
    outdir: Path,
    thresholds: Dict[str, Any],
    *,
    sections_key: str = "json_extract",
    name_json: Optional[str] = None,
    name_csv: Optional[str] = None,
    name_md: Optional[str] = None,
    **kwargs: Any,
) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    """
    UCC step: extract_json_fields

    Expects task_doc[sections_key] like:
      {
        "source_json": "...",
        "fields": [{"id","path","type","required"}, ...],
        "out_json": "extracted_metrics.json",
        "out_csv":  "extracted_metrics.csv",
        "out_md":   "extracted_metrics.md"
      }

    Writes out_json with top-level key "extracted" (required by tests).
    """
    outdir.mkdir(parents=True, exist_ok=True)

    cfg = task_doc.get(sections_key)
    if not isinstance(cfg, dict):
        metrics = {"json_extract_error": f"missing or non-dict section '{sections_key}'"}
        flags = {"json_extract_ok": False}
        return metrics, flags, []

    source_json = cfg.get("source_json", "")
    fields = cfg.get("fields", [])
    if not source_json or not isinstance(source_json, str):
        metrics = {"json_extract_error": "source_json missing/invalid"}
        flags = {"json_extract_ok": False}
        return metrics, flags, []
    if not isinstance(fields, list) or not fields:
        metrics = {"json_extract_error": "fields missing/invalid"}
        flags = {"json_extract_ok": False}
        return metrics, flags, []

    src_path = _resolve_path(source_json)
    if not src_path.exists():
        metrics = {"json_extract_error": f"source_json not found: {src_path}"}
        flags = {"json_extract_ok": False}
        return metrics, flags, []

    data = _load_json(src_path)

    extracted: Dict[str, Any] = {}
    missing_required: List[str] = []
    type_errors: List[str] = []
    path_errors: List[str] = []

    # track per-field info for CSV/MD
    per_field_rows: List[Dict[str, Any]] = []

    for spec in fields:
        if not isinstance(spec, dict):
            continue
        fid = str(spec.get("id", "")).strip()
        path = str(spec.get("path", "")).strip()
        typ = str(spec.get("type", "any")).strip()
        required = bool(spec.get("required", False))

        if not fid or not path:
            if required:
                missing_required.append(fid or "(missing-id)")
            continue

        try:
            parts = _parse_path(path)
        except Exception as e:
            if required:
                path_errors.append(fid)
            per_field_rows.append(
                {"id": fid, "path": path, "type": typ, "required": required, "status": "bad_path", "value": "", "error": str(e)}
            )
            continue

        val = _get_by_parts(data, parts)
        if val is MISSING:
            if required:
                missing_required.append(fid)
            per_field_rows.append(
                {"id": fid, "path": path, "type": typ, "required": required, "status": "missing", "value": "", "error": ""}
            )
            continue

        ok_t, coerced, reason = _coerce_type(val, typ)
        if not ok_t:
            if required:
                type_errors.append(fid)
            per_field_rows.append(
                {"id": fid, "path": path, "type": typ, "required": required, "status": "bad_type", "value": json.dumps(val), "error": reason}
            )
            continue

        extracted[fid] = coerced
        per_field_rows.append(
            {"id": fid, "path": path, "type": typ, "required": required, "status": "ok", "value": json.dumps(coerced), "error": ""}
        )

    ok = (len(missing_required) == 0 and len(type_errors) == 0 and len(path_errors) == 0)

    metrics: Dict[str, Any] = {
        "json_extract_source": str(src_path),
        "json_extract_total_fields": len([f for f in fields if isinstance(f, dict)]),
        "json_extract_extracted": len(extracted),
        "json_extract_missing_required": len(missing_required),
        "json_extract_type_errors": len(type_errors),
        "json_extract_path_errors": len(path_errors),
    }
    flags: Dict[str, Any] = {
        "json_extract_ok": bool(ok),
        "json_extract_missing_required_ids": missing_required,
        "json_extract_type_error_ids": type_errors,
        "json_extract_path_error_ids": path_errors,
    }

    out_json_name = str(cfg.get("out_json") or name_json or "extracted_metrics.json")
    out_csv_name = str(cfg.get("out_csv") or name_csv or "extracted_metrics.csv")
    out_md_name = str(cfg.get("out_md") or name_md or "extracted_metrics.md")

    p_json = outdir / out_json_name
    p_csv = outdir / out_csv_name
    p_md = outdir / out_md_name

    # JSON output must have top-level "extracted" (tests depend on it)
    payload = {
        "extracted": extracted,
        "missing_required": missing_required,
        "type_errors": type_errors,
        "path_errors": path_errors,
        "source_json": str(src_path),
        "metrics": metrics,
        "flags": flags,
    }
    p_json.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    # CSV output (for humans/CI artifacts)
    with p_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["id", "path", "type", "required", "status", "value", "error"])
        for r in per_field_rows:
            w.writerow([r["id"], r["path"], r["type"], str(r["required"]), r["status"], r["value"], r["error"]])

    # Markdown output
    md_lines = [
        "# JSON Extract Fields",
        "",
        f"- source_json: `{src_path}`",
        f"- ok: **{ok}**",
        "",
        "## Extracted",
        "",
        "| id | value | status |",
        "|---|---:|---|",
    ]
    # show extracted first
    for r in per_field_rows:
        val = r["value"]
        md_lines.append(f"| `{r['id']}` | {val} | {r['status']} |")
    md_lines.append("")
    p_md.write_text("\n".join(md_lines), encoding="utf-8")

    return metrics, flags, [p_json, p_csv, p_md]


# Alias for convenience
extract_json_fields = extract_json_fields_task