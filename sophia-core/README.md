# sophia-core v0.1.0

Scaffolding for Sophia’s autonomous oversight agent. This module focuses on two MVP surfaces:

- **Thought Exchange Layer (TEL) hooks** for emitting step-level events.
- **Baseline audit integration** for lightweight governance checks.

## Layout

```
sophia-core/
  README.md
  pyproject.toml
  src/sophia_core/
    __init__.py
    audit.py
    tel.py
    version.py
```

## TEL hook usage

```python
from sophia_core.tel import emit_sophia_event

emit_sophia_event(
    kind="sophia.audit.start",
    data={"run_id": "demo", "stage": "baseline"},
)
```

TEL hooks delegate to `ucc.tel_events.emit_tel_event` when the UCC package is available. Otherwise, the hook is a no-op.

## Baseline audit usage

```python
from sophia_core.audit import run_basic_audit

result = run_basic_audit(telemetry, epistemic_graph)
print(result.decision)
```

The baseline audit currently validates evidence references and highlights missing counterevidence for high-confidence claims.
