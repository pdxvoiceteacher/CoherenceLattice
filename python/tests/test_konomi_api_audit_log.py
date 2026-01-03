from __future__ import annotations

import json
from pathlib import Path
from fastapi.testclient import TestClient

from konomi.api.app import app


def test_audit_log_written(tmp_path, monkeypatch):
    log_path = tmp_path / "audit.jsonl"
    monkeypatch.setenv("KONOMI_AUDIT_LOG", str(log_path))
    monkeypatch.setenv("KONOMI_API_KEY", "auditkey")

    with TestClient(app) as c:
        r = c.post("/v0/process", json={"text":"hi"}, headers={"X-API-Key":"auditkey"})
        assert r.status_code == 200

    lines = log_path.read_text(encoding="utf-8").splitlines()
    assert len(lines) >= 1
    evt = json.loads(lines[-1])

    assert evt["path"] == "/v0/process"
    assert evt["status"] == 200
    assert "api_key_hash" in evt
    assert "api_key" not in evt