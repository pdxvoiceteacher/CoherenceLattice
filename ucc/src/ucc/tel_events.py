from __future__ import annotations
import json, os, threading
from pathlib import Path
from typing import Any, Dict, Optional

_lock = threading.Lock()
_seq = 0

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
    if out is None:
        return
    evt = {"seq": _next_seq(), "kind": str(kind), "data": data}
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("a", encoding="utf-8", newline="\n") as f:
        f.write(_canonical_line(evt))
