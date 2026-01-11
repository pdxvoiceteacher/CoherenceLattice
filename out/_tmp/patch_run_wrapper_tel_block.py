import re
from pathlib import Path

path = Path("tools/telemetry/run_wrapper.py")
text = path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")

# Replace only the TEL post-run emission block (bounded by markers)
pat = re.compile(r"(?s)^(\s*)# --- TEL post-run emission ---.*?^(\s*)# --- /TEL post-run emission ---\s*$", re.M)
m = pat.search(text)
if not m:
    raise SystemExit("Could not find TEL post-run emission markers in run_wrapper.py")

indent = m.group(1)  # indentation level of the marker (likely 4 spaces inside __main__)
block = f"""{indent}# --- TEL post-run emission ---
{indent}if globals().get("_TEL_EMIT", False):
{indent}    def _tel_out_dir(argv):
{indent}        # supports: --out PATH  or  --out=PATH
{indent}        for i, a in enumerate(argv):
{indent}            if a == "--out" and i + 1 < len(argv):
{indent}                return argv[i + 1]
{indent}            if a.startswith("--out="):
{indent}                return a.split("=", 1)[1]
{indent}        return None
{indent}
{indent}    try:
{indent}        from pathlib import Path
{indent}        import json as _json
{indent}        from konomi.tel import TelGraph
{indent}        from konomi.tel.recorder import TelRecorder
{indent}
{indent}        _out = _tel_out_dir(sys.argv)
{indent}        if not _out:
{indent}            raise RuntimeError("TEL requested but --out was not found in argv")
{indent}
{indent}        _out_dir = Path(_out)
{indent}        _telemetry_path = _out_dir / "telemetry.json"
{indent}        if not _telemetry_path.exists():
{indent}            raise FileNotFoundError(f"telemetry.json not found at {{_telemetry_path}}")
{indent}
{indent}        _telemetry_data = _json.loads(_telemetry_path.read_text(encoding="utf-8"))
{indent}
{indent}        # Build TEL graph with explicit checkpoints (deterministic ordering)
{indent}        _tel = TelGraph(graph_id="tel_run_wrapper", meta={{"source": "run_wrapper.py"}})
{indent}        _rec = TelRecorder(_tel)
{indent}
{indent}        _rec.checkpoint("run:telemetry_loaded", meta={{"telemetry_path": str(_telemetry_path)}})
{indent}
{indent}        # Step checkpoints: stage dirs in out/ (sorted) — captures per-step artifacts
{indent}        stage_dirs = []
{indent}        for p in sorted(_out_dir.iterdir(), key=lambda x: x.name):
{indent}            if not p.is_dir():
{indent}                continue
{indent}            name = p.name
{indent}            if name.startswith("konomi_smoke_") or name.startswith("ucc_cov_"):
{indent}                stage_dirs.append(p)
{indent}
{indent}        for stage in stage_dirs:
{indent}            cp = _rec.checkpoint(f"step:{{stage.name}}", meta={{"dir": stage.name}})
{indent}
{indent}            # Attach key artifacts (sorted for determinism)
{indent}            for f in sorted(stage.rglob("*_summary.json"), key=lambda x: x.as_posix()):
{indent}                _rec.attach_file(cp, f, root=_out_dir, kind="summary_json")
{indent}            for f in sorted(stage.rglob("audit_bundle.json"), key=lambda x: x.as_posix()):
{indent}                _rec.attach_file(cp, f, root=_out_dir, kind="audit_bundle")
{indent}
{indent}        # Shallow telemetry tree (kept small) for connectivity
{indent}        _tel.ingest_json_tree(_telemetry_data, root_id="telemetry", max_depth=2)
{indent}        _rec.checkpoint("run:tel_built")
{indent}
{indent}        # Persist full TEL graph
{indent}        _tel.write_json(_out_dir / "tel.json")
{indent}
{indent}        # Embed lean summary into telemetry.json
{indent}        _telemetry_data["tel_summary"] = _tel.summary()
{indent}        (_out_dir / "telemetry.json").write_text(
{indent}            _json.dumps(_telemetry_data, ensure_ascii=False, sort_keys=True, indent=2) + "\\n",
{indent}            encoding="utf-8",
{indent}            newline="\\n",
{indent}        )
{indent}        print("[tel] updated telemetry.json with tel_summary")
{indent}        print(f"[tel] wrote: {{_out_dir / 'tel.json'}}")
{indent}
{indent}    except Exception as _e:
{indent}        print(f"[tel] failed: {{_e}}", file=sys.stderr)
{indent}        raise
{indent}# --- /TEL post-run emission ---"""

text2 = pat.sub(block, text)
path.write_text(text2, encoding="utf-8", newline="\n")
print("patched run_wrapper.py")
