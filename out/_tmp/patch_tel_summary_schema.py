from __future__ import annotations
import json, re, sys
from pathlib import Path

root = Path(sys.argv[1])

# Try to locate schema path from validate_run.py first
schema_path = None
validate = root / "tools" / "telemetry" / "validate_run.py"
if validate.exists():
    txt = validate.read_text(encoding="utf-8")
    rels = re.findall(r'["\']([^"\']+\.schema\.json)["\']', txt)
    rels = [r for r in rels if "telemetry" in r.lower()]
    for rel in rels:
        cand = (root / rel)
        if cand.exists():
            schema_path = cand
            break

# Fallback: search common schema locations
if schema_path is None:
    cands = []
    cands += list(root.rglob("*telemetry*.schema.json"))
    cands += list(root.rglob("*telemetry*schema*.json"))
    cands = sorted(set(cands), key=lambda p: (len(str(p)), str(p)))
    for p in cands:
        try:
            t = p.read_text(encoding="utf-8")
        except Exception:
            continue
        if "coherence_metrics" in t:
            schema_path = p
            break

if schema_path is None:
    raise SystemExit("Could not locate telemetry schema JSON to patch.")

schema = json.loads(schema_path.read_text(encoding="utf-8"))
props = schema.setdefault("properties", {})

tel_summary_schema = {
    "type": "object",
    "required": [
        "schema",
        "tel_schema",
        "graph_id",
        "fingerprint_sha256",
        "nodes_total",
        "edges_total",
        "nodes_by_band",
        "edges_by_kind",
    ],
    "properties": {
        "schema": {"type": "string"},
        "tel_schema": {"type": "string"},
        "graph_id": {"type": "string"},
        "fingerprint_sha256": {"type": "string"},
        "nodes_total": {"type": "integer", "minimum": 0},
        "edges_total": {"type": "integer", "minimum": 0},
        "nodes_by_band": {
            "type": "object",
            "required": ["STM", "MTM", "LTM"],
            "properties": {
                "STM": {"type": "integer", "minimum": 0},
                "MTM": {"type": "integer", "minimum": 0},
                "LTM": {"type": "integer", "minimum": 0},
            },
            "additionalProperties": False,
        },
        "edges_by_kind": {
            "type": "object",
            "additionalProperties": {"type": "integer", "minimum": 0},
        },
        "meta": {"type": "object"},
    },
    "additionalProperties": False,
}

props["tel_summary"] = tel_summary_schema

schema_path.write_text(
    json.dumps(schema, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
    encoding="utf-8",
    newline="\n",
)

print(str(schema_path))
