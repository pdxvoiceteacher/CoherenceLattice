from __future__ import annotations

import json
from pathlib import Path

def test_cis_benchmarks_catalog_exists_and_ids_sane():
    repo = Path(__file__).resolve().parents[1]
    cat = repo / "authorities" / "cis_benchmarks" / "catalog.json"
    data = json.loads(cat.read_text(encoding="utf-8-sig"))
    fams = data.get("families", [])
    assert isinstance(fams, list) and len(fams) > 0

    ids = []
    for f in fams:
        ids.extend(f.get("ids", []))

    assert len(ids) >= 8
    for i in ids:
        assert isinstance(i, str) and i.strip()
        # simple sanity: no lowercase letters
        assert i == i.upper()