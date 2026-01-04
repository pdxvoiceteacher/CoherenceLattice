from __future__ import annotations
from pathlib import Path

FILES = [
    "authorities/mappings/800171_to_80053_family_sample.csv",
    "authorities/mappings/800171_to_soc2_cc_sample.csv",
]

def test_800171_mapping_placeholders_exist():
    repo = Path(__file__).resolve().parents[1]
    for rel in FILES:
        p = repo / rel
        assert p.exists(), f"Missing mapping file: {rel}"
        head = p.read_text(encoding="utf-8-sig").splitlines()[0].strip()
        assert head.startswith("source_authority"), f"Bad header in {rel}"