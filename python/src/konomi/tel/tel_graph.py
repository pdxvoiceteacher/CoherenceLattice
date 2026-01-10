from __future__ import annotations

import base64
import dataclasses
import hashlib
import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Literal, Mapping, Optional, Tuple, Union

MemoryBand = Literal["STM", "MTM", "LTM"]

_HEX_ADDR_RE = re.compile(r"0x[0-9a-fA-F]+")

def _scrub_hex_addrs(s: str) -> str:
    return _HEX_ADDR_RE.sub("0xADDR", s)

def _canonical_dumps(obj: Any, *, indent: int = 2) -> str:
    return (
        json.dumps(obj, ensure_ascii=False, sort_keys=True, indent=indent)
        .replace("\r\n", "\n")
        .replace("\r", "\n")
        + "\n"
    )

def _sort_key_for_any(x: Any) -> str:
    try:
        return _canonical_dumps(x, indent=0)
    except Exception:
        return _scrub_hex_addrs(repr(x))

def _normalize(value: Any) -> Any:
    """
    Best-effort normalization toward JSON-compatible, deterministic structures.

    Supported: primitives, lists/tuples, dicts, sets, dataclasses, Path, bytes
    Unknown objects become {"__type__": "...", "__repr__": "..."} with scrubbed addresses.
    """
    if value is None or isinstance(value, (bool, int, float, str)):
        return value

    if isinstance(value, bytes):
        return {"__bytes_b64__": base64.b64encode(value).decode("ascii")}

    if isinstance(value, Path):
        return str(value)

    if dataclasses.is_dataclass(value):
        return _normalize(dataclasses.asdict(value))

    if isinstance(value, Mapping):
        out: Dict[str, Any] = {}
        for k in sorted((str(k) for k in value.keys())):
            out[k] = _normalize(value[k])
        return out

    if isinstance(value, (list, tuple)):
        return [_normalize(v) for v in value]

    if isinstance(value, set):
        normalized = [_normalize(v) for v in value]
        return sorted(normalized, key=_sort_key_for_any)

    t = f"{value.__class__.__module__}.{value.__class__.__qualname__}"
    rep = _scrub_hex_addrs(repr(value))
    return {"__type__": t, "__repr__": rep}

@dataclass
class TelNode:
    id: str
    band: MemoryBand = "STM"
    payload: Any = None
    meta: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "id": self.id,
            "band": self.band,
            "payload": _normalize(self.payload),
            "meta": _normalize(self.meta),
        }

@dataclass
class TelEdge:
    src: str
    dst: str
    kind: str = "rel"
    weight: Optional[float] = None
    meta: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {
            "src": self.src,
            "dst": self.dst,
            "kind": self.kind,
            "meta": _normalize(self.meta),
        }
        if self.weight is not None:
            d["weight"] = self.weight
        return d

class TelGraph:
    """
    Thought-Exchange Layer (TEL) graph.

    MVP:
      - Flexible symbolic nodes (arbitrary payloads normalized to JSON)
      - Directed edges with optional metadata
      - Memory bands: STM/MTM/LTM
      - Deterministic JSON snapshot (canonical ordering + fingerprint)
    """
    schema: str = "tel_graph_v1"

    def __init__(self, *, graph_id: str = "tel", meta: Optional[Dict[str, Any]] = None):
        self.graph_id = str(graph_id)
        self.meta: Dict[str, Any] = dict(meta or {})
        self._nodes: Dict[str, TelNode] = {}
        self._edges: List[TelEdge] = []

    def add_node(
        self,
        node_id: str,
        *,
        band: MemoryBand = "STM",
        payload: Any = None,
        meta: Optional[Dict[str, Any]] = None,
        overwrite: bool = False,
    ) -> TelNode:
        nid = str(node_id)
        if (nid in self._nodes) and (not overwrite):
            return self._nodes[nid]
        n = TelNode(id=nid, band=band, payload=payload, meta=dict(meta or {}))
        self._nodes[nid] = n
        return n

    def add_edge(
        self,
        src: str,
        dst: str,
        *,
        kind: str = "rel",
        weight: Optional[float] = None,
        meta: Optional[Dict[str, Any]] = None,
    ) -> TelEdge:
        e = TelEdge(src=str(src), dst=str(dst), kind=str(kind), weight=weight, meta=dict(meta or {}))
        self._edges.append(e)
        return e

    def ingest_json_tree(self, obj: Any, *, root_id: str = "root", max_depth: int = 3) -> None:
        self.add_node(root_id, band="STM", payload={"kind": "root"})

        def walk(current: Any, parent_id: str, depth: int) -> None:
            if depth >= max_depth:
                return

            if isinstance(current, Mapping):
                for k in sorted((str(k) for k in current.keys())):
                    child_id = f"{parent_id}.{k}"
                    self.add_node(child_id, band="STM", payload={"key": k})
                    self.add_edge(parent_id, child_id, kind="has_key")
                    walk(current[k], child_id, depth + 1)
                return

            if isinstance(current, list):
                for i, item in enumerate(current):
                    child_id = f"{parent_id}[{i}]"
                    self.add_node(child_id, band="STM", payload={"index": i})
                    self.add_edge(parent_id, child_id, kind="has_index")
                    walk(item, child_id, depth + 1)
                return

            leaf_id = f"{parent_id}.__leaf__"
            self.add_node(leaf_id, band="STM", payload=_normalize(current))
            self.add_edge(parent_id, leaf_id, kind="leaf")

        walk(obj, root_id, 0)

    def to_canonical_dict(self) -> Dict[str, Any]:
        nodes = [self._nodes[k].to_dict() for k in sorted(self._nodes.keys())]

        def edge_sort_key(e: TelEdge) -> Tuple[str, str, str, str, str]:
            w = "" if e.weight is None else f"{e.weight:.12g}"
            meta_dump = _canonical_dumps(_normalize(e.meta), indent=0).strip()
            return (e.src, e.dst, e.kind, w, meta_dump)

        edges = [e.to_dict() for e in sorted(self._edges, key=edge_sort_key)]

        bands: Dict[str, List[str]] = {"STM": [], "MTM": [], "LTM": []}
        for nid in sorted(self._nodes.keys()):
            bands[self._nodes[nid].band].append(nid)

        base = {
            "schema": self.schema,
            "graph_id": self.graph_id,
            "meta": _normalize(self.meta),
            "nodes": nodes,
            "edges": edges,
            "bands": bands,
        }

        fp = hashlib.sha256(_canonical_dumps(base, indent=0).encode("utf-8")).hexdigest()
        base["fingerprint_sha256"] = fp
        return base

    def to_json(self, *, indent: int = 2) -> str:
        return _canonical_dumps(self.to_canonical_dict(), indent=indent)

    def write_json(self, path: Union[str, Path], *, indent: int = 2) -> Path:
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        with p.open("w", encoding="utf-8", newline="\n") as f:
            f.write(self.to_json(indent=indent))
        return p

    def checkpoint(self, out_dir: Union[str, Path], *, filename: Optional[str] = None) -> Path:
        out = Path(out_dir)
        out.mkdir(parents=True, exist_ok=True)
        fp = self.to_canonical_dict()["fingerprint_sha256"]
        name = filename or f"tel_{fp[:12]}.json"
        return self.write_json(out / name)
