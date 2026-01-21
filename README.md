# Sophia Overlay

This repository is a minimal overlay for running Sophia audits against CoherenceLattice/KONOMI outputs.

## Setup

```bash
python -m venv .venv
. .venv/bin/activate
pip install -e sophia-core
pip install -e ucc
```

If you need KONOMI execution support:

```bash
pip install -e python
```

## Generate a run (KONOMI wrapper)

```bash
python tools/telemetry/run_wrapper.py --out out/konami_run --emit-tel --emit-tel-events
```

## Run Sophia audit v3

```bash
python tools/telemetry/sophia_audit.py \
  --run-dir out/konami_run \
  --repo-root . \
  --schema schema/sophia_audit_v3.schema.json \
  --calibrate-trajectories \
  --ethics-check \
  --memory-aware \
  --blockchain-commit \
  --audit-sophia
```

Expected outputs:

- `out/konami_run/sophia_audit.json`
- `out/konami_run/ucc_tel_events.jsonl` (when `--audit-sophia` is used)
- `runs/history/blockchain_anchors.jsonl` (when `--blockchain-commit` is used)
