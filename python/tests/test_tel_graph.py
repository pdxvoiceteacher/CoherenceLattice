import json
from jsonschema import Draft202012Validator

from konomi.tel import TelGraph

TEL_SCHEMA = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "type": "object",
    "required": ["schema", "graph_id", "meta", "nodes", "edges", "bands", "fingerprint_sha256"],
    "properties": {
        "schema": {"type": "string"},
        "graph_id": {"type": "string"},
        "meta": {"type": "object"},
        "fingerprint_sha256": {"type": "string"},
        "nodes": {
            "type": "array",
            "items": {
                "type": "object",
                "required": ["id", "band", "payload", "meta"],
                "properties": {
                    "id": {"type": "string"},
                    "band": {"type": "string", "enum": ["STM", "MTM", "LTM"]},
                    "payload": {},
                    "meta": {"type": "object"},
                },
            },
        },
        "edges": {
            "type": "array",
            "items": {
                "type": "object",
                "required": ["src", "dst", "kind", "meta"],
                "properties": {
                    "src": {"type": "string"},
                    "dst": {"type": "string"},
                    "kind": {"type": "string"},
                    "weight": {"type": "number"},
                    "meta": {"type": "object"},
                },
            },
        },
        "bands": {
            "type": "object",
            "required": ["STM", "MTM", "LTM"],
            "properties": {
                "STM": {"type": "array", "items": {"type": "string"}},
                "MTM": {"type": "array", "items": {"type": "string"}},
                "LTM": {"type": "array", "items": {"type": "string"}},
            },
        },
    },
}

def test_telgraph_json_is_deterministic():
    g1 = TelGraph(graph_id="g")
    g1.add_node("b", band="LTM", payload={"x": 2, "s": set([3, 1, 2])})
    g1.add_node("a", band="STM", payload={"z": 9, "y": 8})
    g1.add_edge("a", "b", kind="supports", meta={"w": set(["c", "a", "b"])})

    g2 = TelGraph(graph_id="g")
    g2.add_node("a", band="STM", payload={"y": 8, "z": 9})
    g2.add_node("b", band="LTM", payload={"s": set([2, 1, 3]), "x": 2})
    g2.add_edge("a", "b", kind="supports", meta={"w": set(["b", "c", "a"])})

    assert g1.to_json() == g2.to_json()

def test_telgraph_schema_shape_and_validates():
    g = TelGraph(graph_id="shape")
    g.add_node("root", band="STM", payload={"hello": "world"})
    g.add_node("mem", band="MTM", payload=[3, 2, 1])
    g.add_edge("root", "mem", kind="references")

    doc = json.loads(g.to_json())
    Draft202012Validator(TEL_SCHEMA).validate(doc)

def test_telgraph_checkpoint_writes_exact_json(tmp_path):
    g = TelGraph(graph_id="cp")
    g.add_node("n1", payload={"k": "v"})
    p = g.checkpoint(tmp_path, filename="tel.json")
    assert p.name == "tel.json"
    assert p.read_text(encoding="utf-8").replace("\r\n", "\n") == g.to_json()
