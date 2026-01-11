import re
from pathlib import Path

p = Path("tools/telemetry/run_wrapper.py")
txt = p.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")

# Ensure import sys exists
if not re.search(r"(?m)^\s*import\s+sys\s*$", txt) and not re.search(r"(?m)^\s*from\s+sys\s+import", txt):
    lines = txt.split("\n")
    import_end = 0
    for i, ln in enumerate(lines):
        if re.match(r"^\s*(import|from)\s+", ln):
            import_end = i + 1
            continue
        if re.match(r"^\s*(def|class)\s+", ln):
            break
    lines = lines[:import_end] + ["import sys"] + lines[import_end:]
    txt = "\n".join(lines)

# Add parser-agnostic stripping of --emit-tel-events next to existing --emit-tel stripping
if "--emit-tel-events" not in txt:
    # Insert after the --emit-tel removal line if present
    lines = txt.split("\n")
    insert_at = None
    for i, ln in enumerate(lines):
        if 'sys.argv.remove("--emit-tel")' in ln:
            insert_at = i + 1
            break
    if insert_at is None:
        # fallback after _TEL_EMIT = False
        for i, ln in enumerate(lines):
            if re.match(r'^\s*_TEL_EMIT\s*=\s*False\s*$', ln):
                insert_at = i + 1
                break
    if insert_at is None:
        raise SystemExit("Could not find a place to insert TEL preparse flags.")

    block = [
        '_TEL_EVENTS_EMIT = False',
        'if "--emit-tel-events" in sys.argv:',
        '    _TEL_EVENTS_EMIT = True',
        '    sys.argv.remove("--emit-tel-events")',
    ]
    lines = lines[:insert_at] + block + lines[insert_at:]
    txt = "\n".join(lines)

# Rewrite TEL post-run emission block safely
pat = re.compile(r"(?s)^(\s*)# --- TEL post-run emission ---.*?^(\s*)# --- /TEL post-run emission ---\s*$", re.M)
m = pat.search(txt)
if not m:
    raise SystemExit("Could not find TEL post-run emission markers in run_wrapper.py")

indent = m.group(1)
i1 = indent + "    "
i2 = i1 + "    "
i3 = i2 + "    "
i4 = i3 + "    "

block = "\n".join([
    indent + "# --- TEL post-run emission ---",
    indent + 'if globals().get("_TEL_EMIT", False) or globals().get("_TEL_EVENTS_EMIT", False):',
    i1 + "def _tel_out_dir(argv):",
    i2 + "# supports: --out PATH  or  --out=PATH",
    i2 + "for i, a in enumerate(argv):",
    i3 + 'if a == \"--out\" and i + 1 < len(argv):',
    i4 + "return argv[i + 1]",
    i3 + 'if a.startswith(\"--out=\"):',
    i4 + 'return a.split(\"=\", 1)[1]',
    i2 + "return None",
    "",
    i1 + "try:",
    i2 + "from pathlib import Path",
    i2 + "import json as _json",
    i2 + "from konomi.tel.build import build_tel_and_events_for_out_dir",
    i2 + "from konomi.tel.events import write_events_jsonl",
    "",
    i2 + "_out = _tel_out_dir(sys.argv)",
    i2 + "if not _out:",
    i3 + 'raise RuntimeError(\"TEL requested but --out was not found in argv\")',
    "",
    i2 + "_out_dir = Path(_out)",
    i2 + '_telemetry_path = _out_dir / \"telemetry.json\"',
    i2 + "if not _telemetry_path.exists():",
    i3 + 'raise FileNotFoundError(f\"telemetry.json not found at {_telemetry_path}\")',
    "",
    i2 + "_telemetry_data = _json.loads(_telemetry_path.read_text(encoding=\"utf-8\"))",
    "",
    i2 + "_tel, _events = build_tel_and_events_for_out_dir(_out_dir, _telemetry_data, max_depth=2)",
    "",
    i2 + 'if globals().get("_TEL_EMIT", False):',
    i3 + '_tel.write_json(_out_dir / \"tel.json\")',
    i3 + '_telemetry_data[\"tel_summary\"] = _tel.summary()',
    i3 + '(_out_dir / \"telemetry.json\").write_text(',
    i4 + '_json.dumps(_telemetry_data, ensure_ascii=False, sort_keys=True, indent=2) + \"\\\\n\",',
    i4 + 'encoding=\"utf-8\",',
    i4 + 'newline=\"\\\\n\",',
    i3 + ")",
    i3 + 'print(\"[tel] updated telemetry.json with tel_summary\")',
    i3 + 'print(f\"[tel] wrote: {_out_dir / \'tel.json\'}\")',
    "",
    i2 + 'if globals().get("_TEL_EVENTS_EMIT", False):',
    i3 + 'write_events_jsonl(_events, _out_dir / \"tel_events.jsonl\")',
    i3 + 'print(f\"[tel_events] wrote: {_out_dir / \'tel_events.jsonl\'}\")',
    "",
    i1 + "except Exception as _e:",
    i2 + 'print(f\"[tel] failed: {_e}\", file=sys.stderr)',
    i2 + "raise",
    indent + "# --- /TEL post-run emission ---",
])

txt2 = pat.sub(block, txt)
p.write_text(txt2, encoding="utf-8", newline="\n")
print("patched run_wrapper.py for --emit-tel-events")
