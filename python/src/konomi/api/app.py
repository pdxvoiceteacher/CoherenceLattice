from __future__ import annotations

import os
from typing import Any, Dict, Optional

from fastapi import Depends, FastAPI, Request, WebSocket, WebSocketDisconnect
from pydantic import BaseModel

from konomi.femto.model import FemtoModel
from konomi.api.security import require_api_key, enforce_rate_limit
from konomi.api.audit import AuditLogger, make_audit_middleware
from konomi.cube.runtime import CubeRuntime, route_index


APP_VERSION = os.getenv("KONOMI_VERSION", "0.1.0-dev")

app = FastAPI(title="KONOMI v0 API (Toy)", version=APP_VERSION)

_audit = AuditLogger()
app.middleware("http")(make_audit_middleware(_audit))

_model = FemtoModel(dim=16, seed=0)
_cube: Optional[CubeRuntime] = None


class ProcessIn(BaseModel):
    text: str


class ProcessOut(BaseModel):
    output: str


class EmbedOut(BaseModel):
    embedding: list[float]


class CubeSendIn(BaseModel):
    key: str
    text: str


class CubeSendOut(BaseModel):
    node: int
    output: str


@app.on_event("startup")
async def _startup() -> None:
    global _cube
    _cube = CubeRuntime(n_nodes=9, queue_max=1024, max_inflight=1024, process_delay_s=0.0)
    await _cube.start()


@app.on_event("shutdown")
async def _shutdown() -> None:
    global _cube
    if _cube is not None:
        await _cube.stop()
        _cube = None


@app.get("/health")
def health() -> Dict[str, Any]:
    return {"ok": True, "version": APP_VERSION}


@app.post("/v0/process", response_model=ProcessOut)
async def process_endpoint(
    req: Request,
    payload: ProcessIn,
    api_key: str = Depends(require_api_key),
) -> ProcessOut:
    enforce_rate_limit(req, api_key)
    out = await _model.process(payload.text)
    return ProcessOut(output=out)


@app.post("/v0/embed", response_model=EmbedOut)
async def embed_endpoint(
    req: Request,
    payload: ProcessIn,
    api_key: str = Depends(require_api_key),
) -> EmbedOut:
    enforce_rate_limit(req, api_key)
    v = await _model.embed(payload.text)
    return EmbedOut(embedding=v)


@app.post("/v0/cube/send", response_model=CubeSendOut)
async def cube_send(
    req: Request,
    payload: CubeSendIn,
    api_key: str = Depends(require_api_key),
) -> CubeSendOut:
    enforce_rate_limit(req, api_key)
    if _cube is None:
        raise RuntimeError("Cube runtime not initialized")
    node = route_index(payload.key, _cube.n_nodes)
    out = await _cube.send(payload.key, payload.text)
    return CubeSendOut(node=node, output=str(out))


@app.websocket("/ws/process")
async def ws_process(ws: WebSocket):
    # Simple API key gating via query param: ?api_key=...
    await ws.accept()
    api_key = ws.query_params.get("api_key", "")
    expected = os.getenv("KONOMI_API_KEY", "devkey")
    if api_key != expected:
        await ws.send_json({"error": "invalid api_key"})
        await ws.close(code=4401)
        return

    try:
        while True:
            msg = await ws.receive_json()
            text = str(msg.get("text", ""))
            out = await _model.process(text)
            await ws.send_json({"output": out})
    except WebSocketDisconnect:
        return