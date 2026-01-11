import json

from konomi.tel import TelGraph, TelRecorder
from konomi.tel.events import events_to_jsonl


def test_tel_events_jsonl_is_deterministic():
    g1 = TelGraph(graph_id="g")
    r1 = TelRecorder(g1)
    cp1 = r1.checkpoint("step:a")
    r1.attach_file(cp1, "x/y/summary.json", root="x", kind="summary_json")

    g2 = TelGraph(graph_id="g")
    r2 = TelRecorder(g2)
    cp2 = r2.checkpoint("step:a")
    r2.attach_file(cp2, "x/y/summary.json", root="x", kind="summary_json")

    assert events_to_jsonl(r1.events) == events_to_jsonl(r2.events)


def test_tel_events_jsonl_parses_linewise():
    g = TelGraph(graph_id="g")
    r = TelRecorder(g)
    cp = r.checkpoint("step:a")
    r.attach_file(cp, "x/y/summary.json", root="x", kind="summary_json")

    s = events_to_jsonl(r.events)
    lines = [ln for ln in s.splitlines() if ln.strip()]
    assert len(lines) > 0

    obj0 = json.loads(lines[0])
    assert "seq" in obj0 and "kind" in obj0 and "data" in obj0
