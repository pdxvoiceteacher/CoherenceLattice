from __future__ import annotations

import json
import math
import re
from pathlib import Path
from typing import Any, Dict, List, Tuple, Optional


# Supports:
#   key = 1.23
#   key == 1.23
#   key: 1.23
#   key ~= 1.23
#   key >= 0
#   key <= 0
#   key > 0
#   key < 0
#   abs(key) <= 0.1
#
# Values support: numbers or true/false
_RE_ABS = re.compile(
    r"""abs\(\s*(?P<key>[A-Za-z][A-Za-z0-9_.]*)\s*\)\s*(?P<op>>=|<=|==|~=|=|>|<|:)\s*(?P<val>true|false|[-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?)""",
    re.IGNORECASE,
)
_RE_PLAIN = re.compile(
    r"""(?P<key>[A-Za-z][A-Za-z0-9_.]*)\s*(?P<op>>=|<=|==|~=|=|>|<|:)\s*(?P<val>true|false|[-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?)""",
    re.IGNORECASE,
)


def _as_list(x: Any) -> List[Any]:
    return x if isinstance(x, list) else []


def _as_dict(x: Any) -> Dict[str, Any]:
    return x if isinstance(x, dict) else {}


def _nonempty_str(x: Any) -> bool:
    return isinstance(x, str) and x.strip() != ""


def _source_local_path(src: Dict[str, Any]) -> Optional[Path]:
    """
    Resolve a local JSON file path from a source entry.
    Prefers url like: local:C:/.../file.json
    """
    url = str(src.get("url", "") or "")
    if url.startswith("local:"):
        p = url[len("local:") :]
        # accept forward slashes on Windows
        return Path(p)
    # If url is already a path-like (rare)
    if url and (":" in url or url.startswith("\\") or url.startswith("/")):
        return Path(url)
    return None


def _load_json_file(path: Path) -> Optional[Dict[str, Any]]:
    try:
        txt = path.read_text(encoding="utf-8-sig")
        obj = json.loads(txt)
        if isinstance(obj, dict):
            return obj
        # Allow top-level arrays by wrapping
        return {"_root": obj}
    except Exception:
        return None


def _extract_values(doc: Dict[str, Any]) -> Dict[str, Any]:
    """
    Extract a lookup table of keys -> values, including:
      - top-level keys
      - metrics.<k> and <k> for doc["metrics"]
      - flags.<k> and <k> for doc["flags"]
    """
    out: Dict[str, Any] = {}

    def add(k: str, v: Any) -> None:
        # Keep bool distinct from numeric
        if isinstance(v, bool):
            out[k] = v
            return
        if isinstance(v, (int, float)) and not isinstance(v, bool) and math.isfinite(float(v)):
            out[k] = float(v)
            return
        if isinstance(v, str):
            out[k] = v

    for k, v in doc.items():
        add(k, v)

    m = doc.get("metrics")
    if isinstance(m, dict):
        for k, v in m.items():
            add(k, v)
            add(f"metrics.{k}", v)

    f = doc.get("flags")
    if isinstance(f, dict):
        for k, v in f.items():
            add(k, v)
            add(f"flags.{k}", v)

    return out


def _parse_val(raw: str) -> Any:
    s = raw.strip().lower()
    if s == "true":
        return True
    if s == "false":
        return False
    # numeric
    return float(raw)


def _tol_ok(actual: float, expected: float, abs_tol: float, rel_tol: float) -> bool:
    return abs(actual - expected) <= max(abs_tol, rel_tol * max(1.0, abs(actual)))


def _cmp(actual: Any, op: str, expected: Any, abs_tol: float, rel_tol: float, use_abs: bool) -> bool:
    op = op.strip()
    if op == ":":
        op = "="

    # bool compare
    if isinstance(expected, bool):
        if not isinstance(actual, bool):
            return False
        if op in ("=", "==", "~="):
            return actual is expected
        return False

    # numeric compare
    if isinstance(expected, (int, float)) and not isinstance(expected, bool):
        if not isinstance(actual, (int, float)) or isinstance(actual, bool):
            return False
        a = float(actual)
        if use_abs:
            a = abs(a)
        e = float(expected)

        if op in ("=", "==", "~="):
            return _tol_ok(a, e, abs_tol, rel_tol)
        if op == ">=":
            return a >= e
        if op == "<=":
            return a <= e
        if op == ">":
            return a > e
        if op == "<":
            return a < e
        return False

    # string compare (rare)
    if isinstance(expected, str):
        if not isinstance(actual, str):
            return False
        if op in ("=", "==", "~="):
            return actual.strip() == expected.strip()
        return False

    return False


def verify_json_assertions_task(
    task_doc: Dict[str, Any],
    outdir: Path,
    thresholds: Dict[str, Any],
    *,
    sections_key: str,
    claims_key: str = "claims",
    sources_key: str = "sources",
    abs_tol: float = 1e-3,
    rel_tol: float = 1e-3,
    require_any: bool = False,
    fail_on_unresolved: bool = True,
    write_json: bool = True,
    write_md: bool = True,
    name_json: str = "json_assertions.json",
    name_md: str = "json_assertions.md",
) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    """
    Parses assertion expressions in claim text and verifies against cited JSON sources.
    Updates metrics/flags for governance-grade traceability.
    """
    outdir.mkdir(parents=True, exist_ok=True)

    artifact = task_doc.get(sections_key)
    if not isinstance(artifact, dict):
        raise ValueError(f"verify_json_assertions requires a dict at task_doc['{sections_key}'].")

    claims = _as_list(artifact.get(claims_key))
    sources = _as_list(artifact.get(sources_key))

    src_by_id: Dict[str, Dict[str, Any]] = {}
    for s in sources:
        if isinstance(s, dict) and _nonempty_str(s.get("id")):
            src_by_id[str(s["id"])] = s

    # cache loaded JSON value maps per source id
    cache: Dict[str, Dict[str, Any]] = {}

    def values_for_source(sid: str) -> Optional[Dict[str, Any]]:
        if sid in cache:
            return cache[sid]
        src = src_by_id.get(sid)
        if not src:
            return None
        p = _source_local_path(src)
        if not p:
            return None
        doc = _load_json_file(p)
        if not doc:
            return None
        vals = _extract_values(doc)
        cache[sid] = vals
        return vals

    assertions_total = 0
    assertions_checked = 0
    assertions_passed = 0
    assertions_failed = 0
    assertions_unresolved = 0

    details: List[Dict[str, Any]] = []

    for c in claims:
        if not isinstance(c, dict):
            continue
        cid = str(c.get("id", ""))
        text = str(c.get("text", "") or "")
        cits = [str(x) for x in _as_list(c.get("citations")) if _nonempty_str(str(x))]

        # find abs() assertions first, then plain
        matches: List[Tuple[str, str, str, bool]] = []
        for m in _RE_ABS.finditer(text):
            matches.append((m.group("key"), m.group("op"), m.group("val"), True))
        for m in _RE_PLAIN.finditer(text):
            matches.append((m.group("key"), m.group("op"), m.group("val"), False))

        if not matches:
            continue

        for key, op, raw_val, use_abs in matches:
            assertions_total += 1
            expected = _parse_val(raw_val)

            # resolve actual from cited JSON sources
            resolved = False
            actual = None
            used_source = None

            for sid in cits:
                vals = values_for_source(sid)
                if not vals:
                    continue
                # direct key or metrics./flags. variants
                if key in vals:
                    actual = vals[key]
                    resolved = True
                    used_source = sid
                    break
                if f"metrics.{key}" in vals:
                    actual = vals[f"metrics.{key}"]
                    resolved = True
                    used_source = sid
                    break
                if f"flags.{key}" in vals:
                    actual = vals[f"flags.{key}"]
                    resolved = True
                    used_source = sid
                    break

            if not resolved:
                assertions_unresolved += 1
                details.append(
                    {
                        "claim_id": cid,
                        "key": key,
                        "op": op,
                        "expected": expected,
                        "resolved": False,
                        "citations": cits,
                    }
                )
                continue

            assertions_checked += 1
            ok = _cmp(actual, op, expected, abs_tol, rel_tol, use_abs)

            if ok:
                assertions_passed += 1
            else:
                assertions_failed += 1

            details.append(
                {
                    "claim_id": cid,
                    "key": key,
                    "op": op,
                    "expected": expected,
                    "actual": actual,
                    "resolved": True,
                    "source_used": used_source,
                    "ok": ok,
                }
            )

    metrics: Dict[str, Any] = {
        "json_assertions_total": assertions_total,
        "json_assertions_checked": assertions_checked,
        "json_assertions_passed": assertions_passed,
        "json_assertions_failed": assertions_failed,
        "json_assertions_unresolved": assertions_unresolved,
        "json_assertions_abs_tol": float(abs_tol),
        "json_assertions_rel_tol": float(rel_tol),
        "json_assertions_require_any": bool(require_any),
        "json_assertions_fail_on_unresolved": bool(fail_on_unresolved),
    }

    flags: Dict[str, Any] = {}
    if require_any and assertions_total == 0:
        flags["json_assertions_ok"] = False
        flags["json_assertions_missing"] = True
    else:
        flags["json_assertions_missing"] = False
        unresolved_bad = (assertions_unresolved > 0) if fail_on_unresolved else False
        flags["json_assertions_ok"] = (assertions_failed == 0) and (not unresolved_bad)

    outputs: List[Path] = []

    if write_json:
        p = outdir / name_json
        p.write_text(
            json.dumps(
                {
                    "schema_version": "0.1",
                    "task": "verify_json_assertions",
                    "metrics": metrics,
                    "flags": flags,
                    "details": details[:200],
                    "details_truncated": len(details) > 200,
                },
                indent=2,
                sort_keys=True,
            ),
            encoding="utf-8",
        )
        outputs.append(p)

    if write_md:
        p = outdir / name_md
        lines = []
        lines.append("# JSON Assertions Check")
        lines.append("")
        lines.append("## Summary")
        lines.append("")
        lines.append(f"- total assertions: **{assertions_total}**")
        lines.append(f"- checked: **{assertions_checked}**")
        lines.append(f"- passed: **{assertions_passed}**")
        lines.append(f"- failed: **{assertions_failed}**")
        lines.append(f"- unresolved: **{assertions_unresolved}**")
        lines.append("")
        lines.append("## Flag")
        lines.append("")
        lines.append(f"- json_assertions_ok: **{flags.get('json_assertions_ok')}**")
        lines.append("")
        lines.append("## Details (first 30)")
        lines.append("")
        lines.append("| claim_id | key | op | expected | actual | source | ok |")
        lines.append("|---|---|---|---:|---:|---|---|")
        for d in details[:30]:
            lines.append(
                f"| {d.get('claim_id','')} | {d.get('key','')} | {d.get('op','')} | "
                f"{d.get('expected','')} | {d.get('actual','')} | {d.get('source_used','')} | {d.get('ok','')} |"
            )
        if len(details) > 30:
            lines.append("")
            lines.append(f"_({len(details)-30} more omitted; see {name_json}.)_")
        p.write_text("\n".join(lines), encoding="utf-8")
        outputs.append(p)

    return metrics, flags, outputs
