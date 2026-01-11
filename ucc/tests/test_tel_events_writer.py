import json, os
from ucc.tel_events import emit_tel_event, reset_seq_for_tests

def test_emit_tel_event_writes_jsonl(tmp_path):
    reset_seq_for_tests()
    p = tmp_path / "ucc_tel_events.jsonl"
    os.environ["UCC_TEL_EVENTS_OUT"] = str(p)
    emit_tel_event("ucc_probe_start", {"ok": True})
    emit_tel_event("ucc_probe_end", {"ok": True})
    assert p.exists()
    lines = [ln for ln in p.read_text(encoding="utf-8").splitlines() if ln.strip()]
    assert len(lines) == 2
    obj0 = json.loads(lines[0])
    assert obj0["seq"] == 1 and "kind" in obj0 and "data" in obj0
