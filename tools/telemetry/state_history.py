#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json
from datetime import datetime, timezone
from pathlib import Path

def load(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-dir", required=True)
    ap.add_argument("--telemetry", required=True)
    ap.add_argument("--state", required=True)
    ap.add_argument("--decision", required=True)
    ap.add_argument("--out", default="out/history/state_history.jsonl")
    ap.add_argument("--max-lines", type=int, default=2000)
    args = ap.parse_args()

    run_dir = Path(args.run_dir)
    tel_p = Path(args.telemetry)
    st_p  = Path(args.state)
    dec_p = Path(args.decision)

    tel = load(tel_p)
    st  = load(st_p)
    dec = load(dec_p)

    rec = {
        "t": datetime.now(timezone.utc).isoformat(),
        "run_dir": str(run_dir).replace("\\","/"),
        "basis": {
            "telemetry_sha256": sha256_file(tel_p),
            "state_sha256": sha256_file(st_p),
            "decision_sha256": sha256_file(dec_p),
        },
        "telemetry_mean": tel.get("metrics", {}),
        "state_mean": st.get("mean", {}),
        "state_sigma": st.get("sigma", {}),
        "risk_band": st.get("risk_band", {}),
        "decision": dec.get("decision", ""),
        "gates": dec.get("gates", {})
    }

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)

    # Append JSONL
    with outp.open("a", encoding="utf-8") as f:
        f.write(json.dumps(rec, sort_keys=True) + "\n")

    # Trim if too long
    try:
        lines = outp.read_text(encoding="utf-8").splitlines()
        if args.max_lines > 0 and len(lines) > args.max_lines:
            lines = lines[-args.max_lines:]
            outp.write_text("\n".join(lines) + "\n", encoding="utf-8")
    except Exception:
        pass

    print(f"[state_history] appended -> {outp}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
