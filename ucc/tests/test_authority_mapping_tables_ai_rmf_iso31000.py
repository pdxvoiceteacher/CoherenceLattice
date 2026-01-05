from __future__ import annotations
from pathlib import Path

FILES = [
    "authorities/mappings/ai_rmf_to_iso42001_sample.csv",
    "authorities/mappings/iso31000_to_nist_csf_sample.csv",
]

def test_mapping_tables_exist_ai_rmf_iso31000():
    repo = Path(__file__).resolve().parents[1]
    for rel in FILES:
        p = repo / rel
        assert p.exists(), f"Missing mapping file: {rel}"
        head = p.read_text(encoding="utf-8-sig").splitlines()[0].strip()
        assert head.startswith("source_authority"), f"Bad header in {rel}"