#!/usr/bin/env python3
"""
scripts/dev_bootstrap.py

Cross-platform bootstrap for CoherenceLattice monorepo:

- Create .venv (optionally recreate)
- Install editable subprojects: ucc, python, coherenceledger_bootstrap
- Install required dependencies (defensive)
- Run pytest suites: ucc/tests and python/tests

Usage:
  python scripts/dev_bootstrap.py
  python scripts/dev_bootstrap.py --recreate-venv
  python scripts/dev_bootstrap.py --skip-tests
  python scripts/dev_bootstrap.py --venv .venv

Notes:
- Always uses the venv interpreter for subsequent operations.
- For CI parity: behaves similarly on Linux/macOS/Windows runners.
"""

from __future__ import annotations

import argparse
import os
import platform
import subprocess
import sys
from pathlib import Path
from typing import List, Optional


def log(msg: str) -> None:
    print(f"[dev_bootstrap] {msg}", flush=True)


def run(cmd: List[str], cwd: Optional[Path] = None) -> None:
    log(" ".join(cmd))
    subprocess.run(cmd, cwd=str(cwd) if cwd else None, check=True)


def try_run(cmd: List[str], cwd: Optional[Path] = None) -> bool:
    try:
        subprocess.run(
            cmd,
            cwd=str(cwd) if cwd else None,
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return True
    except Exception:
        return False


def repo_root() -> Path:
    if try_run(["git", "--version"]):
        try:
            out = subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()
            if out:
                return Path(out)
        except Exception:
            pass
    return Path(__file__).resolve().parents[1]


def venv_python(venv_dir: Path) -> Path:
    if platform.system().lower().startswith("win"):
        return venv_dir / "Scripts" / "python.exe"
    return venv_dir / "bin" / "python"


def ensure_venv(venv_dir: Path, recreate: bool) -> Path:
    py = venv_python(venv_dir)

    if recreate and venv_dir.exists():
        log(f"Recreating venv: removing {venv_dir}")
        import shutil
        shutil.rmtree(venv_dir, ignore_errors=True)

    if not py.exists():
        log(f"Creating venv at {venv_dir}")
        run([sys.executable, "-m", "venv", str(venv_dir)])

    if not py.exists():
        raise RuntimeError(f"Venv python not found at: {py}")

    return py


def pip_install(py: Path, args: List[str], cwd: Path) -> None:
    run([str(py), "-m", "pip"] + args, cwd=cwd)


def pip_install_editable(py: Path, path: str, cwd: Path) -> None:
    pip_install(py, ["install", "-e", path], cwd=cwd)


def install_editable_with_fallback(py: Path, base_path: str, extras: str, cwd: Path) -> None:
    if extras:
        try:
            pip_install_editable(py, f"{base_path}{extras}", cwd=cwd)
            return
        except subprocess.CalledProcessError:
            log(f"Editable install with extras failed: {base_path}{extras} (falling back to {base_path})")
    pip_install_editable(py, base_path, cwd=cwd)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--recreate-venv", action="store_true", help="Delete and recreate venv")
    ap.add_argument("--skip-tests", action="store_true", help="Install only; do not run pytest")
    ap.add_argument("--venv", default=".venv", help="Venv directory path (default: .venv)")
    args = ap.parse_args()

    root = repo_root()
    log(f"Repo root: {root}")
    os.chdir(root)

    # Prevent stale nested venv issues (tests used to prefer python/.venv if present)
    nested = root / "python" / ".venv"
    if nested.exists():
        log("Removing nested python/.venv to prevent interpreter mismatch")
        import shutil
        shutil.rmtree(nested, ignore_errors=True)

    venv_dir = (root / args.venv).resolve()
    py = ensure_venv(venv_dir, recreate=args.recreate_venv)

    log("Upgrading pip")
    pip_install(py, ["install", "--upgrade", "pip"], cwd=root)

    log("Installing editable subprojects")
    install_editable_with_fallback(py, "./ucc", "[dev]", cwd=root)
    install_editable_with_fallback(py, "./python", "[dev]", cwd=root)
    pip_install_editable(py, "./tools/coherenceledger_bootstrap", cwd=root)

    req = ["pytest", "jsonschema", "numpy", "fastapi", "httpx", "cryptography"]
    log(f"Installing required deps (defensive): {', '.join(req)}")
    pip_install(py, ["install"] + req, cwd=root)

    log("Sanity imports")
    run([str(py), "-c", "import coherenceledger, numpy; print('imports OK')"], cwd=root)

    if not args.skip_tests:
        log("Running tests: ucc")
        run([str(py), "-m", "pytest", "-q", "ucc/tests"], cwd=root)

        log("Running tests: python")
        run([str(py), "-m", "pytest", "-q", "python/tests"], cwd=root)
    else:
        log("SkipTests set: not running pytest")

    log("Done")
    log(f"Venv: {venv_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
