from __future__ import annotations

import re
import shutil
import subprocess
import time
from pathlib import Path
from typing import Any, Dict, List, Tuple


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    for _ in range(12):
        if (p / "lakefile.toml").exists() or (p / "lakefile.lean").exists() or (p / "lean-toolchain").exists():
            return p
        if p.parent == p:
            break
        p = p.parent
    raise RuntimeError(f"Could not find Lean repo root above: {start}")


def _validate_import(mod: str) -> str:
    if any(ch.isspace() for ch in mod) or "\n" in mod or "\r" in mod:
        raise ValueError("import_module contains whitespace/newlines")
    if ";" in mod or "#" in mod:
        raise ValueError("import_module contains disallowed characters")
    return mod


def _validate_symbol(sym: str) -> str:
    if any(ch.isspace() for ch in sym) or "\n" in sym or "\r" in sym:
        raise ValueError(f"symbol contains whitespace/newlines: {sym!r}")
    if ";" in sym or sym.startswith("#") or sym.startswith("--"):
        raise ValueError(f"symbol contains disallowed characters: {sym!r}")
    return sym


def _extract_missing(stderr: str) -> List[str]:
    missing: List[str] = []
    pats = [
        r"Unknown constant `([^`]+)`",
        r"Unknown identifier `([^`]+)`",
    ]
    for pat in pats:
        for m in re.findall(pat, stderr):
            missing.append(m)
    seen = set()
    out = []
    for x in missing:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def _decode(b: bytes | None) -> str:
    if not b:
        return ""
    return b.decode("utf-8", errors="replace")


def check_lean_symbols_task(
    task_dir: Path,
    cfg: Dict[str, Any],
    outdir: Path,
    thresholds: Dict[str, Any],
) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    outdir.mkdir(parents=True, exist_ok=True)

    import_module = _validate_import(str(cfg.get("import_module", "CoherenceLattice")))
    symbols = [_validate_symbol(str(s)) for s in list(cfg.get("symbols", []))]
    if not symbols:
        raise ValueError("check_lean_symbols requires non-empty cfg.symbols")

    strict = bool(cfg.get("strict", False))
    timeout_s = int(cfg.get("timeout_s", 30))
    scratch_name = str(cfg.get("scratch_name", "ScratchLeanSymbols.lean"))
    log_name = str(cfg.get("log_name", "lean_check.log"))

    if "repo_root" in cfg and str(cfg["repo_root"]).strip() != "":
        rr = Path(str(cfg["repo_root"]))
        repo_root = rr if rr.is_absolute() else (task_dir / rr).resolve()
    else:
        repo_root = _find_repo_root(task_dir)

    lake = shutil.which("lake") or shutil.which("lake.exe")

    scratch_path = outdir / scratch_name
    log_path = outdir / log_name

    content = "import " + import_module + "\n\n" + "\n".join([f"#check {s}" for s in symbols]) + "\n"
    scratch_path.write_text(content, encoding="utf-8")

    metrics: Dict[str, Any] = {
        "lean_repo_root": str(repo_root),
        "lean_import_module": import_module,
        "lean_symbols_count": len(symbols),
        "lean_symbols": symbols,
    }

    # Always present keys (CI/test friendly)
    flags: Dict[str, Any] = {
        "lean_symbols_skipped": False,
        "lean_symbols_ok": False,
    }

    if lake is None:
        msg = "lake not found on PATH"
        log_path.write_text(msg + "\n", encoding="utf-8")
        metrics.update({"lean_check_status": "skip", "lean_check_reason": msg})
        flags.update({"lean_symbols_skipped": True, "lean_symbols_ok": False})
        if strict:
            flags["lean_symbols_strict_failure"] = True
        return metrics, flags, [scratch_path, log_path]

    t0 = time.time()
    try:
        proc = subprocess.run(
            [lake, "env", "lean", str(scratch_path)],
            cwd=str(repo_root),
            capture_output=True,   # BYTES, not text
            timeout=timeout_s,
        )
        stdout = _decode(proc.stdout)
        stderr = _decode(proc.stderr)
    except subprocess.TimeoutExpired as e:
        stdout = _decode(getattr(e, "stdout", None))
        stderr = _decode(getattr(e, "stderr", None))
        log_path.write_text("TIMEOUT\n\n" + stdout + "\n\n--- STDERR ---\n" + stderr, encoding="utf-8")
        metrics.update({"lean_check_status": "fail", "lean_check_reason": "timeout"})
        flags.update({"lean_symbols_ok": False, "lean_symbols_timeout": True})
        return metrics, flags, [scratch_path, log_path]

    elapsed = time.time() - t0
    log_path.write_text(stdout + "\n\n--- STDERR ---\n" + stderr, encoding="utf-8")

    missing = _extract_missing(stderr)
    ok = (proc.returncode == 0) and (len(missing) == 0)

    metrics.update({
        "lean_check_status": ("pass" if ok else "fail"),
        "lean_check_exit_code": proc.returncode,
        "lean_check_elapsed_s": elapsed,
        "lean_missing_symbols": missing,
    })
    flags.update({
        "lean_symbols_ok": ok,
        "lean_symbols_missing": (len(missing) > 0),
    })

    require_success = bool(thresholds.get("require_success", False))
    if require_success and not ok:
        flags["lean_symbols_threshold_fail"] = True

    return metrics, flags, [scratch_path, log_path]