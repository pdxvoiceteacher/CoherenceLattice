from __future__ import annotations

import numpy as np
from konomi.blockarray.blockarray import BlockArray


def test_get_default_zero():
    ba = BlockArray(shape=(100,100,100), chunk=10)
    assert ba.get(5,5,5) == 0.0


def test_set_get_roundtrip():
    ba = BlockArray(shape=(100,100,100), chunk=10)
    ba.set(5,6,7, 3.5)
    assert abs(ba.get(5,6,7) - 3.5) < 1e-6


def test_set_many():
    ba = BlockArray(shape=(50,50,50), chunk=8)
    coords = np.array([[1,2,3],[10,11,12],[1,2,4],[40,40,40]], dtype=np.int64)
    vals = np.array([1.0,2.0,3.0,4.0], dtype=np.float32)
    ba.set_many(coords, vals)
    assert ba.get(1,2,3) == 1.0
    assert ba.get(10,11,12) == 2.0
    assert ba.get(1,2,4) == 3.0
    assert ba.get(40,40,40) == 4.0


def test_scan_bbox_hits():
    ba = BlockArray(shape=(64,64,64), chunk=8)
    ba.set(10,10,10, 1.0)
    ba.set(20,20,20, 2.0)
    visited, hits, items = ba.scan_bbox(0,32,0,32,0,32, max_blocks=100)
    assert hits >= 2
    assert any((x,y,z)==(10,10,10) for (x,y,z,_) in items)
    assert any((x,y,z)==(20,20,20) for (x,y,z,_) in items)