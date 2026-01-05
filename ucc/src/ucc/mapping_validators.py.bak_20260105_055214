from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Tuple, Set, Optional
import json
import re
import csv

ISO_UTC_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")
SPLIT_TOKENS_RE = re.compile(r"[\s,;]+")

BASE_REQUIRED_COLUMNS = [
    "source_authority",
    "source_id",
    "target_authority",
    "target_id",
    "rationale",
    "evidence_link",
]

def _parse_iso_utc(s: str) -> Optional[datetime]:
    if not isinstance(s, str):
        return None
    ss = s.strip()
    if not ISO_UTC_RE.match(ss):
        return None
    try:
        return datetime.strptime(ss, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
    except Exception:
        return None

def _repo_root() -> Path:
    # .../ucc/src/ucc/mapping_validators.py -> repo root = parents[3]
    return Path(__file__).resolve().parents[3]

def _read_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))

def _load_registry_index(registry_path: Path) -> Dict[str, Any]:
    data = _read_json(registry_path)
    # Support either {authorities:[...]} or {packs:[...]}
    if isinstance(data.get("authorities"), list):
        return {"authorities": data["authorities"]}
    if isinstance(data.get("packs"), list):
        return {"authorities": data["packs"]}
    raise ValueError(f"Invalid registry index: expected 'authorities' or 'packs' list in {registry_path}")

def _collect_ids_from_pack(pack_doc: Any) -> Set[str]:
    ids: Set[str] = set()

    def walk(o: Any) -> None:
        if isinstance(o, dict):
            for k, v in o.items():
                if k == "ids" and isinstance(v, list):
                    for x in v:
                        if isinstance(x, str) and x.strip():
                            ids.add(x.strip())
                else:
                    walk(v)
        elif isinstance(o, list):
            for x in o:
                walk(x)

    walk(pack_doc)
    return ids

def _split_ids(val: Any) -> List[str]:
    if val is None:
        return []
    if isinstance(val, list):
        out: List[str] = []
        for x in val:
            out.extend(_split_ids(x))
        return out
    if not isinstance(val, str):
        return [str(val)]
    s = val.strip()
    if not s:
        return []
    return [t for t in SPLIT_TOKENS_RE.split(s) if t]

def _write_csv(path: Path, rows: List[Dict[str, Any]]) -> None:
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for r in rows:
            w.writerow(r)

def _write_md(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")

@dataclass
class RowResult:
    ok: bool
    errors: List[str]

def validate_mapping_table_task(
    rows: Any,
    outdir: Path,
    thresholds: Dict[str, Any] | None = None,
    *,
    registry_index_path: str = "ucc/authorities/index.json",
    required_columns: List[str] | None = None,
    require_evidence_link: bool = True,
    allow_local_na: bool = True,
    require_review_utc: bool = False,
    require_expires_utc: bool = False,
    enforce_not_expired: bool = True,
    write_validation_md: bool = True,
    write_validation_csv: bool = True,
    md_name: str = "mapping_validation.md",
    csv_name: str = "mapping_validation.csv",
) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    thresholds = thresholds or {}
    outdir.mkdir(parents=True, exist_ok=True)

    if not isinstance(rows, list) or not all(isinstance(r, dict) for r in rows):
        raise ValueError("validate_mapping_table requires ingest_csv; context['input'] must be a list[dict]")

    req_cols = list(required_columns) if required_columns else list(BASE_REQUIRED_COLUMNS)
    if require_review_utc and "review_utc" not in req_cols:
        req_cols.append("review_utc")
    if require_expires_utc and "expires_utc" not in req_cols:
        req_cols.append("expires_utc")

    present_cols: Set[str] = set()
    for r in rows:
        present_cols |= set(r.keys())

    missing_cols = [c for c in req_cols if c not in present_cols]

    repo = _repo_root()
    reg_path = (repo / registry_index_path).resolve()
    reg = _load_registry_index(reg_path)

    # Build authority map id -> entry
    auth_map: Dict[str, Dict[str, Any]] = {}
    for a in reg["authorities"]:
        if isinstance(a, dict) and isinstance(a.get("id"), str):
            auth_map[a["id"]] = a

    # Cache pack IDs by authority id
    id_cache: Dict[str, Set[str]] = {}
    pack_path_cache: Dict[str, str] = {}

    def load_ids_for_authority(aid: str) -> Set[str]:
        if aid in id_cache:
            return id_cache[aid]
        entry = auth_map.get(aid)
        if not entry:
            id_cache[aid] = set()
            return id_cache[aid]
        p = entry.get("path")
        if not isinstance(p, str) or not p.strip():
            id_cache[aid] = set()
            return id_cache[aid]
        pack_path_cache[aid] = p
        pack_doc = _read_json((repo / p).resolve())
        ids = _collect_ids_from_pack(pack_doc)
        id_cache[aid] = ids
        return ids

    now = datetime.now(timezone.utc)

    results: List[RowResult] = []
    unknown_authorities = 0
    unknown_ids = 0
    missing_evidence = 0
    bad_review = 0
    bad_expiry = 0
    expired = 0

    # Validate rows
    for i, r in enumerate(rows, start=1):
        errs: List[str] = []

        # required columns per row
        for c in req_cols:
            if c not in r:
                errs.append(f"missing_column:{c}")

        sa = str(r.get("source_authority", "")).strip()
        ta = str(r.get("target_authority", "")).strip()

        if sa not in auth_map:
            errs.append(f"unknown_source_authority:{sa}")
        if ta not in auth_map:
            errs.append(f"unknown_target_authority:{ta}")

        if sa not in auth_map or ta not in auth_map:
            unknown_authorities += 1

        sids = _split_ids(r.get("source_id", ""))
        tids = _split_ids(r.get("target_id", ""))

        if sa in auth_map:
            allowed = load_ids_for_authority(sa)
            for sid in sids:
                if sid not in allowed:
                    errs.append(f"unknown_source_id:{sid}")
                    unknown_ids += 1

        if ta in auth_map:
            allowed = load_ids_for_authority(ta)
            for tid in tids:
                if tid not in allowed:
                    errs.append(f"unknown_target_id:{tid}")
                    unknown_ids += 1

        if require_evidence_link:
            ev = str(r.get("evidence_link", "")).strip()
            if not ev:
                errs.append("missing_evidence_link")
                missing_evidence += 1
            else:
                if (not allow_local_na) and ev.lower().startswith("local:"):
                    errs.append("evidence_link_disallowed_local")
                    missing_evidence += 1

        if require_review_utc:
            rv = str(r.get("review_utc", "")).strip()
            dt = _parse_iso_utc(rv)
            if dt is None:
                errs.append("bad_review_utc")
                bad_review += 1

        if require_expires_utc:
            ex = str(r.get("expires_utc", "")).strip()
            dt = _parse_iso_utc(ex)
            if dt is None:
                errs.append("bad_expires_utc")
                bad_expiry += 1
            else:
                if enforce_not_expired and dt < now:
                    errs.append("expired_mapping_row")
                    expired += 1

        ok = len(errs) == 0 and len(missing_cols) == 0
        results.append(RowResult(ok=ok, errors=errs))

    rows_ok = sum(1 for rr in results if rr.ok)
    rows_err = len(results) - rows_ok

    mapping_columns_ok = (len(missing_cols) == 0)
    mapping_authorities_ok = (unknown_authorities == 0)
    mapping_ids_ok = (unknown_ids == 0)
    mapping_evidence_ok = (missing_evidence == 0)
    mapping_review_ok = (bad_review == 0) if require_review_utc else True
    mapping_expiry_ok = (bad_expiry == 0 and expired == 0) if require_expires_utc else True

    mapping_table_ok = bool(
        mapping_columns_ok
        and mapping_authorities_ok
        and mapping_ids_ok
        and mapping_evidence_ok
        and mapping_review_ok
        and mapping_expiry_ok
    )

    metrics: Dict[str, Any] = {
        "mapping_rows_total": len(results),
        "mapping_rows_ok": rows_ok,
        "mapping_rows_error": rows_err,
        "missing_required_columns": missing_cols,
        "unknown_authority_count": unknown_authorities,
        "unknown_id_count": unknown_ids,
        "missing_evidence_count": missing_evidence,
        "bad_review_count": bad_review,
        "bad_expiry_count": bad_expiry,
        "expired_count": expired,
        "registry_index_path": str(reg_path),
        "authorities_loaded": len(auth_map),
        "packs_loaded": len([k for k in id_cache.keys() if id_cache[k]]),
    }

    flags: Dict[str, Any] = {
        "mapping_columns_ok": mapping_columns_ok,
        "mapping_authorities_ok": mapping_authorities_ok,
        "mapping_ids_ok": mapping_ids_ok,
        "mapping_evidence_ok": mapping_evidence_ok,
        "mapping_review_ok": mapping_review_ok,
        "mapping_expiry_ok": mapping_expiry_ok,
        "mapping_table_ok": mapping_table_ok,
    }

    out_files: List[Path] = []

    # Write validation CSV
    if write_validation_csv:
        out_rows: List[Dict[str, Any]] = []
        for idx, (r, rr) in enumerate(zip(rows, results), start=1):
            out_rows.append({
                "row": idx,
                "ok": rr.ok,
                "source_authority": r.get("source_authority",""),
                "source_id": r.get("source_id",""),
                "target_authority": r.get("target_authority",""),
                "target_id": r.get("target_id",""),
                "evidence_link": r.get("evidence_link",""),
                "review_utc": r.get("review_utc",""),
                "expires_utc": r.get("expires_utc",""),
                "errors": "|".join(rr.errors),
            })
        csv_path = outdir / csv_name
        _write_csv(csv_path, out_rows)
        out_files.append(csv_path)

    # Write markdown summary
    if write_validation_md:
        lines: List[str] = []
        lines.append("# Mapping Table Validation")
        lines.append("")
        lines.append(f"- rows_total: **{metrics['mapping_rows_total']}**")
        lines.append(f"- rows_ok: **{metrics['mapping_rows_ok']}**")
        lines.append(f"- rows_error: **{metrics['mapping_rows_error']}**")
        lines.append(f"- mapping_table_ok: **{flags['mapping_table_ok']}**")
        lines.append("")
        if missing_cols:
            lines.append("## Missing required columns")
            for c in missing_cols:
                lines.append(f"- {c}")
            lines.append("")
        # show first 10 row errors
        lines.append("## First errors (up to 10 rows)")
        shown = 0
        for idx, rr in enumerate(results, start=1):
            if rr.ok:
                continue
            shown += 1
            lines.append(f"- row {idx}: " + ", ".join(rr.errors))
            if shown >= 10:
                break
        if shown == 0:
            lines.append("- (none)")
        md_path = outdir / md_name
        _write_md(md_path, "\n".join(lines) + "\n")
        out_files.append(md_path)

    return metrics, flags, out_files