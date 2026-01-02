from __future__ import annotations

from fastapi.testclient import TestClient

from konomi.api.app import app


def test_cube_send_ok(monkeypatch):
    monkeypatch.setenv("KONOMI_API_KEY", "cube_key")

    # Using the context manager ensures startup/shutdown events run
    with TestClient(app) as c:
        r = c.post(
            "/v0/cube/send",
            json={"key": "alpha", "text": "hello"},
            headers={"X-API-Key": "cube_key"},
        )
        assert r.status_code == 200
        j = r.json()
        assert "node" in j and isinstance(j["node"], int)
        assert "hello" in j["output"]
