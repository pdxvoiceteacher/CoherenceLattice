from konomi.tel import TelGraph
from konomi.tel.recorder import TelRecorder


def test_telrecorder_checkpoint_determinism():
    g1 = TelGraph(graph_id="g")
    r1 = TelRecorder(g1)
    r1.checkpoint("step:a")
    r1.checkpoint("step:b")

    g2 = TelGraph(graph_id="g")
    r2 = TelRecorder(g2)
    r2.checkpoint("step:a")
    r2.checkpoint("step:b")

    assert g1.to_json() == g2.to_json()


def test_telrecorder_attach_file_is_stable():
    g = TelGraph(graph_id="g")
    r = TelRecorder(g)
    cp = r.checkpoint("step:a")
    f1 = r.attach_file(cp, "x/y/summary.json", root="x")
    f2 = r.attach_file(cp, "x/y/summary.json", root="x")
    assert f1 == f2
