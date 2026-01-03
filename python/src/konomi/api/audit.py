from __future__ import annotations

import json
import os
import time
import uuid
import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Awaitable, Callable, Dict, Optional

from fastapi import Request, Response


def _hash_api_key(api_key: str) -> str:
    if not api_key:
        return ""
    h = hashlib.blake2b(api_key.encode("utf-8"), digest_size=8).hexdigest()
    return h


@dataclass
class AuditLogger:
    """
    Simple JSONL audit logger (demo-quality).
    - Writes one JSON object per line
    - Avoids storing API key plaintext (stores api_key_hash)
    - Path can be overridden by env var KONOMI_AUDIT_LOG at write time
    """
    default_path: str = "kontainer/logs/konomi_audit.jsonl"
    rotate_mb: int = 5

    def _path(self) -> Path:
        p = os.getenv("KONOMI_AUDIT_LOG", self.default_path)
        return Path(p)

    def _rotate_if_needed(self, path: Path) -> None:
        try:
            if not path.exists():
                return
            if path.stat().st_size < self.rotate_mb * 1024 * 1024:
                return
            ts = time.strftime("%Y%m%d_%H%M%S")
            rotated = path.with_suffix(path.suffix + f".{ts}.bak")
            path.rename(rotated)
        except Exception:
            # Never break request flow for logging
            return

    def write(self, event: Dict[str, Any]) -> None:
        path = self._path()
        path.parent.mkdir(parents=True, exist_ok=True)
        self._rotate_if_needed(path)
        with path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(event, ensure_ascii=False) + "\n")


def make_audit_middleware(logger: AuditLogger) -> Callable[[Request, Callable[[Request], Awaitable[Response]]], Awaitable[Response]]:
    async def middleware(request: Request, call_next: Callable[[Request], Awaitable[Response]]) -> Response:
        req_id = str(uuid.uuid4())
        t0 = time.perf_counter_ns()

        api_key = request.headers.get("X-API-Key", "")
        api_key_hash = _hash_api_key(api_key)
        client = request.client.host if request.client else ""

        status = 500
        err_type: Optional[str] = None
        resp: Optional[Response] = None

        try:
            resp = await call_next(request)
            status = int(resp.status_code)
            return resp
        except Exception as e:
            err_type = type(e).__name__
            raise
        finally:
            t1 = time.perf_counter_ns()
            dur_ms = (t1 - t0) / 1e6
            event = {
                "ts_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "request_id": req_id,
                "method": request.method,
                "path": request.url.path,
                "status": status,
                "duration_ms": dur_ms,
                "client": client,
                "api_key_hash": api_key_hash,
                "error_type": err_type,
            }
            logger.write(event)
            if resp is not None:
                resp.headers["X-Request-ID"] = req_id

    return middleware