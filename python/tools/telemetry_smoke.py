from __future__ import annotations

import asyncio
import sys
from pathlib import Path

async def main() -> int:
    repo_root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(repo_root / "python" / "src"))

    import httpx
    from coherence_telemetry_live.server import app

    transport = httpx.ASGITransport(app=app)
    async with httpx.AsyncClient(transport=transport, base_url="http://test") as client:
        r = await client.get("/api/health")
        assert r.status_code == 200, r.text
        print("health:", r.json())

        r2 = await client.get("/api/runs")
        assert r2.status_code == 200, r2.text
        runs = r2.json().get("runs", [])
        print("runs_count:", len(runs))

        if runs:
            run_id = runs[0]["run_id"]
            m = await client.get(f"/api/run/{run_id}/metrics")
            assert m.status_code == 200, m.text
            print("metrics_keys:", list(m.json().keys())[:12])

            a = await client.get(f"/api/run/{run_id}/artifacts")
            assert a.status_code == 200, a.text
            print("artifacts_count:", len(a.json().get("artifacts", [])))

    print("SMOKE OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(asyncio.run(main()))