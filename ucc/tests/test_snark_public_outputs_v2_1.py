import json
from pathlib import Path
import pytest

from ucc.snark_public_outputs import public_signals_from_public_json, PublicOutputError


def test_public_json_mapping_derives_choice_hash(tmp_path: Path):
    order = ["manifest_id","ballot_id","nullifier_sha256","ciphertext_sha256","aad_sha256","choice_hash"]
    values = ["m","b","n","c","a","h"]
    p = tmp_path / "public.json"
    p.write_text(json.dumps(values), encoding="utf-8")

    m = public_signals_from_public_json(p, order)
    assert m["choice_hash"] == "h"
    assert m["ballot_id"] == "b"


def test_public_json_too_short_rejected(tmp_path: Path):
    order = ["a","b","c"]
    values = ["1"]
    p = tmp_path / "public.json"
    p.write_text(json.dumps(values), encoding="utf-8")

    with pytest.raises(PublicOutputError):
        public_signals_from_public_json(p, order)
