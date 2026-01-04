from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Dict, List, Tuple, Optional


# Pattern assertions embedded in claim text:
#   key ~ /regex/flags
#   key !~ /regex/flags
# flags: i,m,s (optional)
# Example:
#   environment.git_commit ~ /^[0-9a-f]{40}$/i
#   module.sha256 ~ /^[0-9a-f]{64}$/
#
_RE = re.compile(
    r"""(?P<key>[A-Za-z][A-Za-z0-9_.]*)\s*(?P<op>!~|~)\s*/(?P<pat>(?:\\\/|[^/])*)/(?P<flags>[imsIMS]*)""",
    re.IGNORECASE,
)


def _as_list(x: Any) -> List[Any]:
    return x if isinstance(x, list) else []


def _nonempty_str(x: Any) -> bool:
    return isinstance(x, str) and x.strip() != ""


def _source_local_path(src: Dict[str, Any]) -> Optional[Path]:
    url = str(src.get("url", "") or "")
    if url.startswith("local:"):
        return Path(url[len("local:") :])
    return None


def _load_json_file(path: Path) -> Optional[Dict[str, Any]]:
    try:
        txt = path.read_text(encoding="utf-8-sig")
        obj = json.loads(txt)
        if isinstance(obj, dict):
            return obj
        return {"_root": obj}
    except Exception:
        return None


def _flatten(doc: Any, prefix: str = "", out: Optional[Dict[str, Any]] = None, max_depth: int = 8) -> Dict[str, Any]:
    if out is None:
        out = {}
    if max_depth <= 0:
        return out

    if isinstance(doc, dict):
        for k, v in doc.items():
            if not isinstance(k, str):
                continue
            key = f"{prefix}.{k}" if prefix else k
            _flatten(v, key, out, max_depth - 1)
        return out

    # Keep primitives (string/bool/number) as leaf values
    if isinstance(doc, (str, bool, int, float)) and not (isinstance(doc, float) and (doc != doc)):  # not NaN
        out[prefix] = doc
        return out

    # Ignore lists/other types (could be added later)
    return out


def _extract_values(doc: Dict[str, Any]) -> Dict[str, Any]:
    """
    Build a lookup of dot-path keys -> primitive leaf values, plus convenience:
      metrics.<k>, flags.<k>, and direct <k> for metrics/flags entries.
    """
    out = _flatten(doc)

    m = doc.get("metrics")
    if isinstance(m, dict):
        for k, v in m.items():
            if isinstance(k, str) and isinstance(v, (str, bool, int, float)):
                out[k] = v
                out[f"metrics.{k}"] = v

    f = doc.get("flags")
    if isinstance(f, dict):
        for k, v in f.items():
            if isinstance(k, str) and isinstance(v, (str, bool, int, float)):
                out[k] = v
                out[f"flags.{k}"] = v

    return out


def _compile_pattern(pat_raw: str, flags_raw: str) -> re.Pattern[str]:
    pat = pat_raw.replace(r"\/", "/")
    flags = 0
    f = flags_raw.lower()
    if "i" in f:
        flags |= re.IGNORECASE
    if "m" in f:
        flags |= re.MULTILINE
    if "s" in f:
        flags |= re.DOTALL
    return re.compile(pat, flags)


def verify_json_patterns_task(
    task_doc: Dict[str, Any],
    outdir: Path,
    thresholds: Dict[str, Any],
    *,
    sections_key: str,
    claims_key: str = "claims",
    sources_key: str = "sources",
    require_any: bool = False,
    fail_on_unresolved: bool = True,
    write_json: bool = True,
    write_md: bool = True,
    name_json: str = "json_patterns.json",
    name_md: str = "json_patterns.md",
) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    outdir.mkdir(parents=True, exist_ok=True)

    artifact = task_doc.get(sections_key)
    if not isinstance(artifact, dict):
        raise ValueError(f"verify_json_patterns requires a dict at task_doc['{sections_key}'].")

    claims = _as_list(artifact.get(claims_key))
    sources = _as_list(artifact.get(sources_key))

    src_by_id: Dict[str, Dict[str, Any]] = {}
    for s in sources:
        if isinstance(s, dict) and _nonempty_str(s.get("id")):
            src_by_id[str(s["id"])] = s

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

    total = checked = passed = failed = unresolved = 0
    details: List[Dict[str, Any]] = []

    for c in claims:
        if not isinstance(c, dict):
            continue
        cid = str(c.get("id", ""))
        text = str(c.get("text", "") or "")
        cits = [str(x) for x in _as_list(c.get("citations")) if _nonempty_str(str(x))]

        matches = list(_RE.finditer(text))
        if not matches:
            continue

        for m in matches:
            total += 1
            key = m.group("key")
            op = m.group("op")
            pat_raw = m.group("pat")
            flags_raw = m.group("flags") or ""

            # resolve actual from cited sources
            actual = None
            used = None
            for sid in cits:
                vals = values_for_source(sid)
                if not vals:
                    continue
                if key in vals:
                    actual = vals[key]
                    used = sid
                    break
                # tolerate metrics/flags prefix too
                if f"metrics.{key}" in vals:
                    actual = vals[f"metrics.{key}"]
                    used = sid
                    break
                if f"flags.{key}" in vals:
                    actual = vals[f"flags.{key}"]
                    used = sid
                    break

            if actual is None:
                unresolved += 1
                details.append({"claim_id": cid, "key": key, "op": op, "pattern": f"/{pat_raw}/{flags_raw}", "resolved": False, "citations": cits})
                continue

            checked += 1
            actual_s = str(actual)

            try:
                rx = _compile_pattern(pat_raw, flags_raw)
                hit = rx.search(actual_s) is not None
            except Exception as e:
                failed += 1
                details.append({"claim_id": cid, "key": key, "op": op, "pattern": f"/{pat_raw}/{flags_raw}", "actual": actual_s, "source_used": used, "ok": False, "error": str(e)})
                continue

            ok = (hit if op == "~" else (not hit))
            if ok:
                passed += 1
            else:
                failed += 1

            details.append({"claim_id": cid, "key": key, "op": op, "pattern": f"/{pat_raw}/{flags_raw}", "actual": actual_s, "source_used": used, "ok": ok})

    metrics: Dict[str, Any] = {
        "json_patterns_total": total,
        "json_patterns_checked": checked,
        "json_patterns_passed": passed,
        "json_patterns_failed": failed,
        "json_patterns_unresolved": unresolved,
        "json_patterns_require_any": bool(require_any),
        "json_patterns_fail_on_unresolved": bool(fail_on_unresolved),
    }

    flags: Dict[str, Any] = {}
    if require_any and total == 0:
        flags["json_patterns_ok"] = False
        flags["json_patterns_missing"] = True
    else:
        flags["json_patterns_missing"] = False
        unresolved_bad = (unresolved > 0) if fail_on_unresolved else False
        flags["json_patterns_ok"] = (failed == 0) and (not unresolved_bad)

    outputs: List[Path] = []

    if write_json:
        p = outdir / name_json
        p.write_text(
            json.dumps(
                {
                    "schema_version": "0.1",
                    "task": "verify_json_patterns",
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
        lines.append("# JSON Pattern Checks")
        lines.append("")
        lines.append("## Summary")
        lines.append("")
        lines.append(f"- total patterns: **{total}**")
        lines.append(f"- checked: **{checked}**")
        lines.append(f"- passed: **{passed}**")
        lines.append(f"- failed: **{failed}**")
        lines.append(f"- unresolved: **{unresolved}**")
        lines.append("")
        lines.append("## Flag")
        lines.append("")
        lines.append(f"- json_patterns_ok: **{flags.get('json_patterns_ok')}**")
        lines.append("")
        lines.append("## Details (first 30)")
        lines.append("")
        lines.append("| claim_id | key | op | pattern | actual | source | ok |")
        lines.append("|---|---|---|---|---|---|---|")
        for d in details[:30]:
            lines.append(
                f"| {d.get('claim_id','')} | {d.get('key','')} | {d.get('op','')} | {d.get('pattern','')} | "
                f"{d.get('actual','')} | {d.get('source_used','')} | {d.get('ok','')} |"
            )
        if len(details) > 30:
            lines.append("")
            lines.append(f"_({len(details)-30} more omitted; see {name_json}.)_")
        p.write_text("\n".join(lines), encoding="utf-8")
        outputs.append(p)

    return metrics, flags, outputs


# Alias
verify_json_patterns = verify_json_patterns_task