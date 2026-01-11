from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Optional, Union

from .tel_graph import TelGraph, MemoryBand


def _stable_file_id(rel_path: str) -> str:
    h = hashlib.sha256(rel_path.encode("utf-8")).hexdigest()
    return h[:12]


@dataclass
class TelRecorder:
    """
    Append-only recorder that writes cognition checkpoints into a TelGraph.

    Design goals:
      - deterministic IDs (sequence + sorted discovery upstream)
      - lightweight per-step checkpoint nodes
      - optional file attachments as artifact nodes
    """
    graph: TelGraph
    default_band: MemoryBand = "STM"
    _counter: int = 0
    _last_checkpoint_id: Optional[str] = None

    def checkpoint(
        self,
        label: str,
        *,
        band: Optional[MemoryBand] = None,
        payload: Any = None,
        meta: Optional[Dict[str, Any]] = None,
        link_from_last: bool = True,
        edge_kind: str = "next",
    ) -> str:
        self._counter += 1
        node_id = f"cp_{self._counter:05d}"
        node_payload: Dict[str, Any] = {"kind": "checkpoint", "label": str(label)}
        if payload is not None:
            node_payload["payload"] = payload

        self.graph.add_node(
            node_id,
            band=(band or self.default_band),
            payload=node_payload,
            meta=dict(meta or {}),
        )

        if link_from_last and self._last_checkpoint_id is not None:
            self.graph.add_edge(self._last_checkpoint_id, node_id, kind=edge_kind)

        self._last_checkpoint_id = node_id
        return node_id

    def attach_file(
        self,
        parent_checkpoint_id: str,
        path: Union[str, Path],
        *,
        root: Optional[Union[str, Path]] = None,
        kind: str = "artifact",
        meta: Optional[Dict[str, Any]] = None,
        band: MemoryBand = "MTM",
    ) -> str:
        p = Path(path)
        r = Path(root) if root is not None else None
        rel = str(p.relative_to(r) if r is not None else p).replace("\\", "/")

        node_id = f"file_{_stable_file_id(rel)}"
        self.graph.add_node(
            node_id,
            band=band,
            payload={"kind": "file", "path": rel, "role": kind},
            meta=dict(meta or {}),
            overwrite=False,
        )
        self.graph.add_edge(parent_checkpoint_id, node_id, kind=f"file:{kind}")
        return node_id
