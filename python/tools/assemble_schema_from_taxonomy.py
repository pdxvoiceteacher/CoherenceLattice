from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict, List, Tuple

def read_json(p: Path) -> Any:
    return json.loads(p.read_text(encoding="utf-8"))

def write_json(p: Path, obj: Any) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")

def unescape_ptr(seg: str) -> str:
    # RFC 6901
    return seg.replace("~1", "/").replace("~0", "~")

def split_pointer(ptr: str) -> List[str]:
    if not isinstance(ptr, str) or not ptr.startswith("/"):
        raise ValueError(f"invalid JSON pointer: {ptr!r}")
    parts = ptr.lstrip("/").split("/")
    return [unescape_ptr(x) for x in parts if x != ""]

def set_at_pointer(root: Dict[str, Any], ptr: str, value: Any, source: str) -> None:
    parts = split_pointer(ptr)
    cur: Any = root
    for k in parts[:-1]:
        if not isinstance(cur, dict):
            raise ValueError(f"cannot traverse pointer {ptr} at {k} (non-object) from {source}")
        if k not in cur:
            cur[k] = {}
        if not isinstance(cur[k], dict):
            raise ValueError(f"cannot traverse pointer {ptr} at {k} (existing non-object) from {source}")
        cur = cur[k]

    last = parts[-1] if parts else None
    if last is None:
        raise ValueError(f"empty pointer not supported: {ptr}")

    if not isinstance(cur, dict):
        raise ValueError(f"cannot set pointer {ptr} (parent non-object) from {source}")

    if last in cur and cur[last] != value:
        raise ValueError(f"pointer collision at {ptr}: existing differs (source={source})")
    cur[last] = value

def base_schema_template() -> Dict[str, Any]:
    # Base keys that are stable across engines
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "telemetry_v1.schema.json",
        "title": "CoherenceLattice Telemetry Metrics v1 (generated)",
        "type": "object",
        "additionalProperties": False,
        "required": [],  # filled later
        "properties": {
            "schema_version": {"type": "string", "const": "telemetry.v1"},
            "run_id": {"type": "string", "pattern": "^[0-9a-f]{12}$"},
            "generated_utc": {"type": "string"}
        }
    }

def collect_top_level_required(modules: List[Dict[str, Any]]) -> List[str]:
    req = {"schema_version", "run_id", "generated_utc"}
    for m in modules:
        metrics = m.get("metrics", {}) if isinstance(m, dict) else {}
        owns = metrics.get("owns", []) or []
        for ptr in owns:
            if isinstance(ptr, str) and ptr.startswith("/properties/"):
                # only direct children of /properties become top-level required
                rest = ptr[len("/properties/"):]
                if "/" not in rest and rest:
                    req.add(rest)
    return sorted(req)

def ensure_required_present(schema: Dict[str, Any]) -> None:
    props = schema.get("properties", {})
    if not isinstance(props, dict):
        raise ValueError("schema missing properties object")
    missing = [k for k in (schema.get("required") or []) if k not in props]
    if missing:
        raise ValueError(f"required keys missing from properties: {missing}")

def optional_check_schema(schema: Dict[str, Any]) -> None:
    try:
        import jsonschema  # type: ignore
        jsonschema.Draft202012Validator.check_schema(schema)
    except ImportError:
        return
    except Exception as e:
        raise ValueError(f"jsonschema check_schema failed: {e}") from e

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--taxonomy-dir", default="", help="defaults to paper/schema/telemetry_taxonomy")
    ap.add_argument("--registry", default="registry.json")
    ap.add_argument("--out", default="", help="override output path relative to repo root (default from registry.schema_root)")
    ap.add_argument("--check", action="store_true", help="run jsonschema.check_schema if jsonschema is installed")
    ap.add_argument("--print", action="store_true", help="print generated schema to stdout instead of writing")
    args = ap.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    tax_dir = Path(args.taxonomy_dir) if args.taxonomy_dir else (repo_root / "paper" / "schema" / "telemetry_taxonomy")
    reg_path = tax_dir / args.registry

    if not reg_path.exists():
        raise SystemExit(f"missing taxonomy registry: {reg_path}")

    reg = read_json(reg_path)
    if "modules" not in reg or not isinstance(reg["modules"], list):
        raise SystemExit("registry.json missing modules[]")

    if args.out:
        out_path = (repo_root / args.out).resolve()
    else:
        schema_root = reg.get("schema_root")
        if not isinstance(schema_root, str) or not schema_root:
            raise SystemExit("registry.json missing schema_root")
        out_path = (tax_dir / schema_root).resolve()

    modules_loaded: List[Dict[str, Any]] = []
    fragments: List[Tuple[str, Dict[str, Any], str]] = []  # (ptr, schema, source)

    for item in reg["modules"]:
        if not isinstance(item, dict):
            raise SystemExit("registry.modules entry must be object")
        eid = item.get("engine_id")
        rel = item.get("path")
        if not isinstance(eid, str) or not isinstance(rel, str):
            raise SystemExit("registry.modules entries require engine_id and path")
        mp = tax_dir / rel
        if not mp.exists():
            raise SystemExit(f"module file missing: {mp}")
        mod = read_json(mp)
        modules_loaded.append(mod)

        metrics = mod.get("metrics", {}) if isinstance(mod, dict) else {}
        frs = metrics.get("schema_fragments", []) or []
        if not isinstance(frs, list):
            raise SystemExit(f"{eid}: metrics.schema_fragments must be list")

        for fr in frs:
            if not isinstance(fr, dict):
                raise SystemExit(f"{eid}: schema_fragments entry must be object")
            ptr = fr.get("json_pointer")
            sch = fr.get("schema")
            if not isinstance(ptr, str) or not ptr.startswith("/"):
                raise SystemExit(f"{eid}: invalid schema_fragments.json_pointer: {ptr!r}")
            if not isinstance(sch, dict):
                raise SystemExit(f"{eid}: schema_fragments.schema must be object")
            fragments.append((ptr, sch, f"{eid}:{ptr}"))

    schema = base_schema_template()

    # Apply all fragments (no collisions expected if validate_taxonomy.py is green)
    for ptr, sch, source in fragments:
        set_at_pointer(schema, ptr, sch, source)

    # Derived top-level required list from ownership declarations
    schema["required"] = collect_top_level_required(modules_loaded)
    ensure_required_present(schema)

    if args.check:
        optional_check_schema(schema)

    if args.print:
        print(json.dumps(schema, indent=2, sort_keys=True))
    else:
        write_json(out_path, schema)
        print(f"Wrote schema: {out_path}")
        print(f"modules={len(modules_loaded)} fragments={len(fragments)} required={len(schema['required'])}")

    return 0

if __name__ == "__main__":
    raise SystemExit(main())