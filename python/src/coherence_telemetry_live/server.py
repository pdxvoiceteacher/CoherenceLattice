from __future__ import annotations

import asyncio
import json
import os
from pathlib import Path
from typing import Any, Dict, List

from fastapi import FastAPI, WebSocket, WebSocketDisconnect, HTTPException
from fastapi.responses import HTMLResponse, JSONResponse, FileResponse
from fastapi.staticfiles import StaticFiles

APP_VERSION = "0.1.1"

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_RUNS_ROOT = REPO_ROOT / "paper" / "out" / "runs"
RUNS_ROOT = Path(os.environ.get("COHERENCE_RUNS_ROOT", str(DEFAULT_RUNS_ROOT)))

STATIC_DIR = Path(__file__).resolve().parent / "static"

app = FastAPI(title="Coherence Telemetry Live", version=APP_VERSION)

if STATIC_DIR.exists():
    app.mount("/static", StaticFiles(directory=str(STATIC_DIR)), name="static")

def list_runs() -> List[Dict[str, Any]]:
    if not RUNS_ROOT.exists():
        return []
    dirs = [d for d in RUNS_ROOT.iterdir() if d.is_dir()]
    dirs.sort(key=lambda p: p.stat().st_mtime, reverse=True)
    out: List[Dict[str, Any]] = []
    for d in dirs:
        st = d.stat()
        out.append({"run_id": d.name, "path": str(d), "mtime": st.st_mtime})
    return out

def run_dir(run_id: str) -> Path:
    return RUNS_ROOT / run_id

def read_json_safe(p: Path) -> Dict[str, Any]:
    if not p.exists():
        return {"error": "missing", "path": str(p)}
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception as e:
        return {"error": "json_parse", "path": str(p), "detail": str(e)}

@app.get("/")
async def root() -> Any:
    idx = STATIC_DIR / "index.html"
    if idx.exists():
        return HTMLResponse(idx.read_text(encoding="utf-8"))
    return JSONResponse({"status": "ok", "message": "No static index.html found.", "runs_root": str(RUNS_ROOT)})

@app.get("/api/health")
def health() -> Dict[str, Any]:
    return {"status": "ok", "version": APP_VERSION, "runs_root": str(RUNS_ROOT)}

@app.get("/api/runs")
def api_runs() -> Dict[str, Any]:
    return {"runs": list_runs()}

@app.get("/api/runs/summaries")
def api_runs_summaries(n: int = 20) -> Dict[str, Any]:
    runs = list_runs()[: max(1, min(int(n), 200))]
    summaries: List[Dict[str, Any]] = []
    for r in runs:
        m = read_json_safe(Path(r["path"]) / "metrics.json")
        guft = m.get("guft", {}) if isinstance(m, dict) else {}
        tok = m.get("telemetry_ok", {}) if isinstance(m, dict) else {}
        summaries.append({
            "run_id": r["run_id"],
            "mtime": r["mtime"],
            "psi": guft.get("psi"),
            "E": guft.get("E"),
            "T": guft.get("T"),
            "all_ok": tok.get("all_ok"),
        })
    return {"summaries": summaries}

@app.get("/api/run/{run_id}/metrics")
def api_metrics(run_id: str) -> Dict[str, Any]:
    return read_json_safe(run_dir(run_id) / "metrics.json")

@app.get("/api/run/{run_id}/manifest")
def api_manifest(run_id: str) -> Dict[str, Any]:
    return read_json_safe(run_dir(run_id) / "manifest.json")

@app.get("/api/run/{run_id}/artifacts")
def api_artifacts(run_id: str) -> Dict[str, Any]:
    ad = run_dir(run_id) / "artifacts"
    if not ad.exists():
        return {"artifacts": []}
    files = []
    for f in sorted(ad.glob("*")):
        if f.is_file():
            files.append({"name": f.name, "bytes": f.stat().st_size})
    return {"artifacts": files}

@app.get("/api/run/{run_id}/artifact/{name}")
def api_artifact(run_id: str, name: str) -> Any:
    p = run_dir(run_id) / "artifacts" / name
    if not p.exists():
        raise HTTPException(status_code=404, detail=f"artifact not found: {name}")
    mt = "text/csv" if name.lower().endswith(".csv") else "application/octet-stream"
    return FileResponse(str(p), media_type=mt, filename=name)

@app.get("/api/run/{run_id}/events_tail")
def api_events_tail(run_id: str, n: int = 50) -> Dict[str, Any]:
    p = run_dir(run_id) / "events.jsonl"
    if not p.exists():
        return {"lines": [], "n": n}
    lines = p.read_text(encoding="utf-8").splitlines()
    return {"lines": lines[-n:], "n": n}

@app.websocket("/ws")
async def ws(ws: WebSocket) -> None:
    await ws.accept()
    try:
        qp = ws.query_params
        run_id = qp.get("run_id")
        from_start = (qp.get("from_start", "0").lower() in ("1", "true", "yes"))
        poll = float(qp.get("poll", "0.5"))

        if not run_id:
            runs = list_runs()
            if not runs:
                await ws.send_text(json.dumps({"type": "error", "error": "no runs found", "runs_root": str(RUNS_ROOT)}))
                await ws.close()
                return
            run_id = runs[0]["run_id"]

        rd = run_dir(run_id)
        events_path = rd / "events.jsonl"
        metrics_path = rd / "metrics.json"

        await ws.send_text(json.dumps({"type": "hello", "run_id": run_id, "run_dir": str(rd), "from_start": from_start, "poll": poll}))

        if metrics_path.exists():
            await ws.send_text(json.dumps({"type": "metrics", "metrics": read_json_safe(metrics_path)}))

        offset = 0
        if not from_start and events_path.exists():
            offset = events_path.stat().st_size

        last_metrics_mtime = metrics_path.stat().st_mtime if metrics_path.exists() else 0.0

        while True:
            if events_path.exists():
                with open(events_path, "rb") as f:
                    f.seek(offset)
                    data = f.read()
                    offset = f.tell()
                if data:
                    for raw in data.splitlines():
                        txt = raw.decode("utf-8", errors="replace")
                        try:
                            obj = json.loads(txt)
                            await ws.send_text(json.dumps({"type": "event", "event": obj}))
                        except Exception:
                            await ws.send_text(json.dumps({"type": "event_raw", "line": txt}))

            if metrics_path.exists():
                mtime = metrics_path.stat().st_mtime
                if mtime > last_metrics_mtime:
                    last_metrics_mtime = mtime
                    await ws.send_text(json.dumps({"type": "metrics", "metrics": read_json_safe(metrics_path)}))

            await asyncio.sleep(poll)

    except WebSocketDisconnect:
        return
    except Exception as e:
        try:
            await ws.send_text(json.dumps({"type": "error", "error": str(e)}))
        finally:
            try:
                await ws.close()
            except Exception:
                pass