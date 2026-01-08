from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Protocol


class SnarkBackend(Protocol):
    def verify(self, *, alg: str, proof_b64: str, public_signals: Dict[str, Any], vk_bytes: bytes) -> None:
        ...


@dataclass(frozen=True)
class DisabledBackend:
    def verify(self, *, alg: str, proof_b64: str, public_signals: Dict[str, Any], vk_bytes: bytes) -> None:
        raise NotImplementedError("SNARK backend disabled (configure a backend to enable Groth16/PLONK verification).")


def get_backend_from_env() -> SnarkBackend:
    # v1.1: always disabled; v1.2 will add subprocess backends.
    return DisabledBackend()
