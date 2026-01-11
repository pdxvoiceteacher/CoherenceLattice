import re
from pathlib import Path
import sys

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")

# If already patched, do nothing
if "_tel_sanitize_for_schema" in text and "TEL_SUMMARY_SCHEMA" in text:
    print(str(path))
    raise SystemExit(0)

# Helper block inserted after imports
helper = r"""
# --- TEL summary handling (optional) ---
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

def _tel_sanitize_for_schema(instance):
    """
    If instance is a dict with tel_summary:
      - validate tel_summary against TEL_SUMMARY_SCHEMA
      - return a shallow copy with tel_summary removed (so telemetry root schema remains strict)
    Otherwise return instance unchanged.
    """
    if not isinstance(instance, dict):
        return instance

    if "tel_summary" not in instance:
        return instance

    tel = instance.get("tel_summary")
    if tel is not None:
        Draft202012Validator(TEL_SUMMARY_SCHEMA).validate(tel)

    inst2 = dict(instance)
    inst2.pop("tel_summary", None)
    return inst2
# --- /TEL summary handling (optional) ---
"""

# Insert helper after imports
lines = text.split("\n")
import_end = 0
for i, ln in enumerate(lines):
    if re.match(r"^\s*(import|from)\s+", ln):
        import_end = i + 1
        continue
    if re.match(r"^\s*(def|class)\s+", ln):
        break

lines = lines[:import_end] + [""] + helper.strip("\n").split("\n") + [""] + lines[import_end:]
text = "\n".join(lines).rstrip("\n") + "\n"

# Patch any single-line calls like:
#   validator.iter_errors(X)
#   validator.validate(X)
# by wrapping X with _tel_sanitize_for_schema(...)
out_lines = []
for ln in text.split("\n"):
    if "_tel_sanitize_for_schema" in ln:
        out_lines.append(ln)
        continue

    for meth in (".iter_errors(", ".validate("):
        pos = ln.find(meth)
        if pos != -1:
            # insert wrapper right after '('
            open_paren = pos + len(meth) - 1
            # find matching ')' for this call on the same line
            depth = 0
            end = None
            for j in range(open_paren, len(ln)):
                ch = ln[j]
                if ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0:
                        end = j
                        break
            if end is not None:
                ln = ln[:open_paren+1] + "_tel_sanitize_for_schema(" + ln[open_paren+1:end] + ")" + ln[end:]
    out_lines.append(ln)

patched = "\n".join(out_lines).rstrip("\n") + "\n"
path.write_text(patched, encoding="utf-8", newline="\n")
print(str(path))
