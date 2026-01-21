from __future__ import annotations

import importlib.util
from dataclasses import dataclass
from typing import Any, Dict, Optional, Protocol


@dataclass(frozen=True)
class TelEvent:
    kind: str
    data: Dict[str, Any]


class TelHook(Protocol):
    def emit(self, event: TelEvent) -> None:
        ...


def _ucc_emit_available() -> bool:
    return importlib.util.find_spec("ucc.tel_events") is not None


if _ucc_emit_available():
    from ucc.tel_events import emit_tel_event as _ucc_emit_tel_event
else:
    def _ucc_emit_tel_event(kind: str, data: Dict[str, Any]) -> None:
        return None


def emit_sophia_event(kind: str, data: Optional[Dict[str, Any]] = None) -> None:
    payload = data or {}
    _ucc_emit_tel_event(kind, payload)


def emit_hook_event(hook: Optional[TelHook], event: TelEvent) -> None:
    if hook is None:
        return
    hook.emit(event)
