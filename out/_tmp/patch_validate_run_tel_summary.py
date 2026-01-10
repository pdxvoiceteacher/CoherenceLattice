import re
from pathlib import Path
import sys

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")

# Remove any misplaced early calls to _maybe_inject_tel_summary(...)
lines = []
for ln in text.split("\n"):
    if re.match(r"^\s*_maybe_inject_tel_summary\s*\(", ln):
        continue
    lines.append(ln)
text = "\n".join(lines).rstrip("\n") + "\n"

helper = r"""
# --- TEL summary schema (optional) ---
TEL_SUMMARY_SCHEMA = {
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

def _inject_tel_summary_schema_inplace(schema_obj: dict) -> None:
    if not isinstance(schema_obj, dict):
        return
    props = schema_obj.setdefault("properties", {})
    if isinstance(props, dict) and "tel_summary" not in props:
        props["tel_summary"] = TEL_SUMMARY_SCHEMA
# --- /TEL summary schema (optional) ---
"""

# Ensure helper exists (insert after imports)
if "TEL_SUMMARY_SCHEMA" not in text or "_inject_tel_summary_schema_inplace" not in text:
    # after last import/from before first def/class
    import_end = 0
    lines = text.split("\n")
    for i, ln in enumerate(lines):
        if re.match(r"^\s*(import|from)\s+", ln):
            import_end = i + 1
            continue
        if re.match(r"^\s*(def|class)\s+", ln):
            break
    lines = lines[:import_end] + [""] + helper.strip("\n").split("\n") + [""] + lines[import_end:]
    text = "\n".join(lines).rstrip("\n") + "\n"

# Find the first Draft202012Validator( ... ) *call* and extract its first positional arg
m = re.search(r"Draft202012Validator\s*\(", text)
if not m:
    raise SystemExit("Could not find Draft202012Validator( call")

call_pos = text.find("(", m.start())
depth = 0
end = None
for i in range(call_pos, len(text)):
    ch = text[i]
    if ch == "(":
        depth += 1
    elif ch == ")":
        depth -= 1
        if depth == 0:
            end = i
            break
if end is None:
    raise SystemExit("Could not parse Draft202012Validator(...) call")

arg_text = text[call_pos+1:end].strip()
arg0 = arg_text.split(",", 1)[0].strip()
if not arg0:
    raise SystemExit("Could not determine schema argument to Draft202012Validator(...)")

# Insert injection line immediately before the line containing the call
line_start = text.rfind("\n", 0, m.start()) + 1
indent = re.match(r"[ \t]*", text[line_start:]).group(0)

# Avoid duplicate injection near the call
window = text[max(0, line_start-400):line_start]
if "_inject_tel_summary_schema_inplace" not in window:
    inject_line = f"{indent}_inject_tel_summary_schema_inplace({arg0})\n"
    text = text[:line_start] + inject_line + text[line_start:]

path.write_text(text, encoding="utf-8", newline="\n")
print(str(path))
