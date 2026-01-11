from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, Literal, Mapping, Sequence, Union

TelEventKind = Literal["checkpoint", "edge", "attach_file", "note"]

@dataclass(frozen=True)
class TelEvent:
    seq: int
    kind: str
    data: Dict[str, Any]

    def to_dict(self) -> Dict[str, Any]:
        return {"seq": self.seq, "kind": self.kind, "data": self.data}

def _canonical_json(obj: Any) -> str:
    # Deterministic single-line JSON (ideal for JSONL)
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":"))

def events_to_jsonl(events: Sequence[Union[TelEvent, Mapping[str, Any]]]) -> str:
    lines = []
    for e in events:
        d = e.to_dict() if isinstance(e, TelEvent) else dict(e)
        lines.append(_canonical_json(d))
    return "\n".join(lines) + "\n"

def write_events_jsonl(events: Sequence[Union[TelEvent, Mapping[str, Any]]], path: Union[str, Path]) -> Path:
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(events_to_jsonl(events), encoding="utf-8", newline="\n")
    return p
