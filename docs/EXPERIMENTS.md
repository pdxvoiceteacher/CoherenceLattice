# Experiment Suite Overview

The experiments below provide a concrete, runnable pathway for verifying the CoherenceLattice formal invariants and telemetry pipelines. Each experiment includes a purpose, a procedure, and expected artifacts.

## Experiment 0 — Build & Verify (“The project is real”)

**Purpose**: Confirm the repo builds, proofs compile, and Python tests pass.

**Procedure**:

```bash
# 1) Lean proofs
lake build

# 2) Python tests (repo root)
python -m pytest

# 3) Demo ingestion pipeline (unguided + guided)
python tools/telemetry/ingest_submission.py --submission-dir examples/submission_demo --repo-root .
```

**Expected outputs**:
- `lake build` succeeds (Lean proofs verify).
- `pytest` passes.
- `examples/submission_demo/ingest_report.json` contains `status: ok` for both runs.

## Experiment 1 — Guided vs Unguided Baseline (Dual Run Demo)

**Purpose**: Demonstrate parallel guided vs unguided runs with governance artifacts.

**Procedure**:

```bash
python tools/telemetry/ingest_submission.py --submission-dir examples/submission_demo --repo-root .
```

**Expected outputs**:
- Guided and unguided runs remain deterministic.
- `runs/guided/sophia_audit.json` shows governance checks; unguided is minimal.
- `runs/*/telemetry.json` show comparable metrics; guided should not inflate DeltaS/Lambda.

## Experiment 2 — Λ Gate Trigger (Forced Criticality)

### 2A — Deterministic Lambda Spike (Low compute)

**Purpose**: Inject a known Lambda value (≥ 0.80) and trigger a lambda gate event.

**Procedure**:

```bash
# 1) Generate telemetry runs with a guided Lambda spike
python tools/telemetry/generate_lambda_spike.py --submission-dir examples/submission_lambda_spike

# 2) Optional: run the UCC module that reads the spike artifact
python -m ucc.cli run ucc/modules/experiments/lambda_spike.yml \
  --input ucc/tasks/experiments/lambda_spike_task.json \
  --outdir ucc/out/experiments/lambda_spike

# 3) Ingest the submission for schema and audit checks
python tools/telemetry/ingest_submission.py --submission-dir examples/submission_lambda_spike --repo-root .
```

**Expected outputs**:
- `examples/submission_lambda_spike/runs/guided/telemetry.json` has `Lambda ≈ 0.85`.
- `examples/submission_lambda_spike/runs/guided/ucc_tel_events.jsonl` includes `lambda_gate: review`.

### 2B — Optional High-Λ from Drift (Higher compute)

**Purpose**: Trigger Lambda via actual drift/perturbations.

**Procedure** (optional):

```bash
python tools/telemetry/run_wrapper.py --out out/telemetry_lambda_hi --perturbations 8
```

**Expected outputs**:
- If perturbation drift is large enough, `telemetry.json` reports a higher Lambda.
- If Lambda < 0.80, the gate will not trigger (expected for benign workloads).

## Experiment 3 — No-Teleport Regime Adjacency Demo

**Purpose**: Operationally show that bounded updates do not skip regimes.

**Procedure**:

```bash
python tools/telemetry/demo_no_teleport.py --out out/demo_no_teleport.json
```

**Expected outputs**:
- `out/demo_no_teleport.json` shows stepwise regime changes with adjacency-only transitions.
- Script exits non-zero if a non-adjacent transition is detected.

## Experiment 4 — ΔSyn Exogenic Offloading Demo

**Purpose**: Show guided governance reduces missing-evidence burden (ΔS proxy).

**Procedure**:

```bash
python -m ucc.cli run ucc/modules/coherence_audit.yml \
  --input ucc/tasks/experiments/offloading_incomplete.json \
  --outdir ucc/out/experiments/offloading_incomplete

python -m ucc.cli run ucc/modules/coherence_audit.yml \
  --input ucc/tasks/experiments/offloading_complete.json \
  --outdir ucc/out/experiments/offloading_complete
```

**Expected outputs**:
- `offloading_incomplete` report flags missing sections/evidence (lower T/E, higher ΔS).
- `offloading_complete` report passes required evidence and sections.

## Experiment 5 — Logos Translation Test (Structure Enforcement)

**Purpose**: Enforce required structured output sections.

**Procedure**:

```bash
python -m ucc.cli run ucc/modules/experiments/logos_required_sections.yml \
  --input ucc/tasks/experiments/logos_missing_sections.json \
  --outdir ucc/out/experiments/logos_missing

python -m ucc.cli run ucc/modules/experiments/logos_required_sections.yml \
  --input ucc/tasks/experiments/logos_complete.json \
  --outdir ucc/out/experiments/logos_complete
```

**Expected outputs**:
- `logos_missing` checklist reports missing sections.
- `logos_complete` checklist reports full coverage.

## Experiment 6 — Lean ↔ Telemetry Correspondence Map

| Lean theorem / invariant | Lean source | Runtime check / artifact | Where to observe |
| --- | --- | --- | --- |
| Ψ bounded in [0,1] | `psi_nonneg`, `psi_le_one` | Telemetry schema bounds for `Psi` | `schema/telemetry/telemetry_run.schema.json` + `tools/telemetry/validate_run.py` |
| No-Teleport (bounded ΔΨ) | `validTransition_of_abs_lt_tau0` | Regime adjacency demo | `tools/telemetry/demo_no_teleport.py` output |
| stepET bounded drift | `abs_psi_stepET_sub_le` | Stepwise ΔΨ cap in demo | `tools/telemetry/demo_no_teleport.py` uses `coherence_sim.model` thresholds |
| stepPsi/stepET valid transitions | `validTransition_stepPsi`, `validTransition_stepET` | Regime transitions logged in demo | `tools/telemetry/demo_no_teleport.py` |
| Λ bounded [0,1] | `Coherence.Lambda` (formalization) | Telemetry schema bounds for `Lambda` | `schema/telemetry/telemetry_run.schema.json` + `tools/telemetry/validate_run.py` |
| Λ gate behavior | N/A (operational) | Lambda gate event | `tools/telemetry/run_wrapper.py` / `examples/submission_lambda_spike/runs/guided/ucc_tel_events.jsonl` |

