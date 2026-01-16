from __future__ import annotations
import json, os, threading
from pathlib import Path
from typing import Any, Dict, Optional

_lock = threading.Lock()
_seq = 0
def emit_tel_event(kind: str, data: Dict[str, Any]) -> None:

def reset_seq_for_tests() -> None:
    global _seq
    with _lock:
        _seq = 0

def _next_seq() -> int:
    global _seq
    with _lock:
        _seq += 1
        return _seq

def _canonical_line(obj: Any) -> str:
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n"

def _out_path() -> Optional[Path]:
    v = os.environ.get("UCC_TEL_EVENTS_OUT", "").strip()
    if not v:
        return None
    return Path(v)

def emit_tel_event(kind: str, data: Dict[str, Any]) -> None:
    out = _out_path()
        # DEBUG (temporary): prove emit_tel_event is being called
    if os.environ.get("UCC_TEL_DEBUG", "").strip() == "1":
        print("[UCC TEL DEBUG] emit_tel_event called:", kind)

    if out is None:
        return

    # --- Lambda Gate annotation (safe additive metadata) ---
    try:
        # Candidate locations for metrics:
        cm = None
        if isinstance(data.get("coherence_metrics"), dict):
            cm = data["coherence_metrics"]
        elif isinstance(data.get("metrics"), dict):
            cm = data["metrics"]
        else:
            cm = data

        # Recognize all lambda key variants used in this repo:
        lam = None
        if isinstance(cm, dict):
            lam = cm.get("Λ", cm.get("lambda", cm.get("Lambda", cm.get("Lambda_T"))))

        if lam is not None:
            meta = data.get("meta")
            if not isinstance(meta, dict):
                meta = {}
                data["meta"] = meta
            meta["lambda"] = float(lam)
            meta["lambda_warn"] = 0.80
            meta["lambda_gate"] = "review" if float(lam) >= 0.80 else "proceed"
    except Exception:
        pass
    # --- /Lambda Gate annotation ---

    evt = {"seq": _next_seq(), "kind": str(kind), "data": data}
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("a", encoding="utf-8", newline="\n") as f:
        f.write(_canonical_line(evt))
