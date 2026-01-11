from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Protocol, Optional
from pathlib import Path
import base64
import json
import os
import subprocess
import tempfile

from ucc.public_inputs import to_snarkjs_public_inputs

from ucc.proof_formats import to_snarkjs_proof


class SnarkBackend(Protocol):
    def verify(self, *, alg: str, proof_b64: str, public_signals: Dict[str, Any], vk_bytes: bytes) -> None:
        ...


@dataclass(frozen=True)
class DisabledBackend:
    def verify(self, *, alg: str, proof_b64: str, public_signals: Dict[str, Any], vk_bytes: bytes) -> None:
        raise NotImplementedError("SNARK backend disabled (set UCC_SNARK_ALLOW_SUBPROCESS=1 and UCC_SNARK_BACKEND=snarkjs).")


def _truthy(v: str) -> bool:
    return v.strip().lower() in {"1", "true", "yes", "y", "on"}


def _in_ci() -> bool:
    # Hard block: never run external tooling in CI
    return _truthy(os.getenv("GITHUB_ACTIONS", "0")) or _truthy(os.getenv("CI", "0"))


def _snark_timeout() -> int:
    try:
        return int(os.getenv("UCC_SNARK_TIMEOUT_SECS", "20"))
    except Exception:
        return 20


def _max_err() -> int:
    try:
        return int(os.getenv("UCC_SNARK_MAX_STDERR", "4000"))
    except Exception:
        return 4000



def _public_inputs_for_snarkjs(public_signals: Dict[str, Any]) -> Any:
    """
    snarkjs expects public inputs as a JSON array (usually strings).
    We support:
      - public_signals['public_inputs'] as list
      - env UCC_SNARK_PUBLIC_SIGNAL_ORDER="k1,k2,..." to build an ordered list from dict
    """
    if isinstance(public_signals.get("public_inputs"), list):
        return public_signals["public_inputs"]

    order = os.getenv("UCC_SNARK_PUBLIC_SIGNAL_ORDER", "").strip()
    if order:
        keys = [k.strip() for k in order.split(",") if k.strip()]
        arr = []
        for k in keys:
            if k not in public_signals:
                raise ValueError(f"public_signals missing ordered key: {k}")
            arr.append(public_signals[k])
        return arr

    raise ValueError(
        "snarkjs backend needs public_signals['public_inputs'] list OR UCC_SNARK_PUBLIC_SIGNAL_ORDER to build an ordered array"
    )


@dataclass(frozen=True)
class SnarkjsBackend:
    """
    Subprocess backend for snarkjs.
    Requires:
      UCC_SNARK_ALLOW_SUBPROCESS=1
      UCC_SNARK_BACKEND=snarkjs
    Optional:
      UCC_SNARKJS_BIN=snarkjs  (or full path to snarkjs/snarkjs.cmd)
      UCC_SNARK_TIMEOUT_SECS=20
      UCC_SNARK_MAX_STDERR=4000
      UCC_SNARK_PUBLIC_SIGNAL_ORDER=manifest_id,ballot_id,... (only if you don't provide public_inputs)
    """
    snarkjs_bin: str = "snarkjs"

    def verify(self, *, alg: str, proof_b64: str, public_signals: Dict[str, Any], vk_bytes: bytes) -> None:
        if _in_ci():
            raise NotImplementedError("Refusing to run subprocess SNARK backend in CI/GitHub Actions.")

        proof_obj = to_snarkjs_proof(proof_b64, expected_alg=alg_u)
        strict_inputs = _truthy(os.getenv('UCC_SNARK_STRICT_PUBLIC_INPUTS','1'))
        public_inputs = to_snarkjs_public_inputs(public_signals, strict=strict_inputs)

        alg_u = alg.upper().strip()
        if alg_u not in {"GROTH16", "PLONK"}:
            raise NotImplementedError(f"snarkjs backend supports GROTH16/PLONK only (got {alg_u})")

        with tempfile.TemporaryDirectory(prefix="ucc_snarkjs_") as d:
            td = Path(d)

            vk_path = td / "vk.json"
            proof_path = td / "proof.json"
            public_path = td / "public.json"

            vk_path.write_bytes(vk_bytes)
            proof_path.write_text(json.dumps(proof_obj), encoding="utf-8")
            public_path.write_text(json.dumps(public_inputs), encoding="utf-8")

            # snarkjs commands:
            #   snarkjs groth16 verify vk.json public.json proof.json
            #   snarkjs plonk   verify vk.json public.json proof.json
            cmd = [self.snarkjs_bin, alg_u.lower(), "verify", str(vk_path), str(public_path), str(proof_path)]

            try:
                proc = subprocess.run(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    timeout=_snark_timeout(),
                    check=False,
                )
            except subprocess.TimeoutExpired:
                raise TimeoutError("snarkjs verify timed out")

            if proc.returncode != 0:
                err = (proc.stderr or "")[-_max_err():]
                raise ValueError(f"snarkjs verify failed (rc={proc.returncode}): {err}")

            # snarkjs prints messages; we accept rc==0 as pass.
            return


def get_backend_from_env() -> SnarkBackend:
    """
    Gate rules:
      - NEVER run in CI (GITHUB_ACTIONS/CI truthy) -> DisabledBackend
      - Must set UCC_SNARK_ALLOW_SUBPROCESS=1 to enable
      - UCC_SNARK_BACKEND selects implementation (snarkjs supported)
    """
    if _in_ci():
        return DisabledBackend()

    if not _truthy(os.getenv("UCC_SNARK_ALLOW_SUBPROCESS", "0")):
        return DisabledBackend()

    backend = os.getenv("UCC_SNARK_BACKEND", "").strip().lower()
    if backend == "snarkjs":
        return SnarkjsBackend(snarkjs_bin=os.getenv("UCC_SNARKJS_BIN", "snarkjs"))

    # Unknown or unset -> disabled
    return DisabledBackend()
