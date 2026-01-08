from ucc.proof_formats import wrap_proof, b64_encode_json, to_snarkjs_proof


def test_snarkjs_wrapper_roundtrip_groth16():
    proof_obj = {"pi_a":[1,2], "pi_b":[[1,2],[3,4]], "pi_c":[5,6]}
    proof_b64 = b64_encode_json(wrap_proof("snarkjs.groth16.v1", proof_obj))
    out = to_snarkjs_proof(proof_b64, expected_alg="GROTH16")
    assert out["pi_a"] == [1,2]
