import pytest

from ucc.public_inputs import build_public_inputs_spec, to_snarkjs_public_inputs, PublicInputsError


def test_build_and_decode_spec():
    ps = {
        "manifest_id":"m",
        "ballot_id":"b",
        "nullifier_sha256":"n",
        "ciphertext_sha256":"c",
        "aad_sha256":"a",
        "choice_hash":"h",
    }
    spec = build_public_inputs_spec(ps)
    ps2 = dict(ps)
    ps2["public_inputs"] = spec

    arr = to_snarkjs_public_inputs(ps2, strict=True)
    assert arr == ["m","b","n","c","a","h"]


def test_strict_rejects_legacy_list():
    ps = {"public_inputs": ["1","2"]}
    with pytest.raises(PublicInputsError):
        to_snarkjs_public_inputs(ps, strict=True)
