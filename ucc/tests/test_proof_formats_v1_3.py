import pytest

from ucc.proof_formats import wrap_proof, b64_encode_json, to_snarkjs_proof, ProofFormatError


def test_snarkjs_groth16_shape_ok():
    p = wrap_proof("snarkjs.groth16.v1", {"pi_a":[1,2], "pi_b":[[1,2],[3,4]], "pi_c":[5,6]})
    b64 = b64_encode_json(p)
    obj = to_snarkjs_proof(b64, expected_alg="GROTH16")
    assert "pi_a" in obj


def test_snarkjs_groth16_shape_missing_key_fails():
    p = wrap_proof("snarkjs.groth16.v1", {"pi_a":[1,2], "pi_b":[[1,2],[3,4]]})
    b64 = b64_encode_json(p)
    with pytest.raises(ProofFormatError):
        to_snarkjs_proof(b64, expected_alg="GROTH16")


def test_snarkjs_plonk_shape_ok():
    p = wrap_proof("snarkjs.plonk.v1", {"proof":"abc"})
    b64 = b64_encode_json(p)
    obj = to_snarkjs_proof(b64, expected_alg="PLONK")
    assert "proof" in obj


def test_alg_format_mismatch_fails():
    p = wrap_proof("snarkjs.plonk.v1", {"proof":"abc"})
    b64 = b64_encode_json(p)
    with pytest.raises(ProofFormatError):
        to_snarkjs_proof(b64, expected_alg="GROTH16")
