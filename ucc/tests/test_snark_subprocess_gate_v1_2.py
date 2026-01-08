import pytest

from ucc.snark_backend import get_backend_from_env


def test_backend_disabled_without_allow(monkeypatch):
    monkeypatch.delenv("UCC_SNARK_ALLOW_SUBPROCESS", raising=False)
    monkeypatch.setenv("UCC_SNARK_BACKEND", "snarkjs")
    b = get_backend_from_env()
    with pytest.raises(NotImplementedError):
        b.verify(alg="GROTH16", proof_b64="", public_signals={}, vk_bytes=b"{}")


def test_backend_refuses_in_ci(monkeypatch):
    monkeypatch.setenv("UCC_SNARK_ALLOW_SUBPROCESS", "1")
    monkeypatch.setenv("UCC_SNARK_BACKEND", "snarkjs")
    monkeypatch.setenv("GITHUB_ACTIONS", "1")  # simulate CI
    b = get_backend_from_env()
    with pytest.raises(NotImplementedError):
        b.verify(alg="GROTH16", proof_b64="", public_signals={}, vk_bytes=b"{}")
