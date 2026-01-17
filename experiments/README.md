# Experiments

## Lambda spike 2A (minimal)

### Windows (PowerShell)

```powershell
.\.venv\Scripts\python.exe -m ucc.cli run `
  experiments\lambda_spike_2a\module.yml `
  --input experiments\lambda_spike_2a\ucc_input.json `
  --outdir out\lambda_spike_2a_test
```

### Linux/macOS

```bash
. .venv/bin/activate
python -m ucc.cli run experiments/lambda_spike_2a/module.yml --input experiments/lambda_spike_2a/ucc_input.json --outdir out/lambda_spike_2a_test
```

## Experiment 1: Lambda_T from Series

### Windows (PowerShell)

```powershell
.\.venv\Scripts\python.exe -m ucc.cli run `
  experiments\exp1_lambda_from_series\module.yml `
  --input experiments\exp1_lambda_from_series\input.json `
  --outdir out\exp1_lambda_from_series_20260117
```

Expected outputs: `ucc_report.json`, `thresholds.csv`, `thresholds.md`, `audit_bundle.json`.

### Linux/macOS

```bash
. .venv/bin/activate
python -m ucc.cli run experiments/exp1_lambda_from_series/module.yml --input experiments/exp1_lambda_from_series/input.json --outdir out/exp1_lambda_from_series_20260117
```

## Experiment 3: No-Teleport Lean Symbols

### Windows (PowerShell)

```powershell
.\.venv\Scripts\python.exe -m ucc.cli run `
  experiments\exp3_no_teleport\module.yml `
  --input experiments\exp3_no_teleport\input.json `
  --outdir out\exp3_no_teleport_20260117
```

Expected outputs: `ucc_report.json`, `audit_bundle.json`, plus `ScratchLeanSymbols.lean` and `lean_check.log`.
If lake is not on PATH, the Lean check returns skip (not failure). Install Lean toolchain / lake to enable strict validation.

### Linux/macOS

```bash
. .venv/bin/activate
python -m ucc.cli run experiments/exp3_no_teleport/module.yml --input experiments/exp3_no_teleport/input.json --outdir out/exp3_no_teleport_20260117
```

## Experiment 4: Evidence Gate

### Windows (PowerShell)

```powershell
.\.venv\Scripts\python.exe -m ucc.cli run `
  experiments\exp4_evidence_gate\module.yml `
  --input experiments\exp4_evidence_gate\input.json `
  --outdir out\exp4_evidence_gate_20260117
```

Expected outputs: `ucc_report.json`, `audit_bundle.json`.

### Linux/macOS

```bash
. .venv/bin/activate
python -m ucc.cli run experiments/exp4_evidence_gate/module.yml --input experiments/exp4_evidence_gate/input.json --outdir out/exp4_evidence_gate_20260117
```

## Experiment 5: Required Sections

### Windows (PowerShell)

```powershell
.\.venv\Scripts\python.exe -m ucc.cli run `
  experiments\exp5_required_sections\module.yml `
  --input experiments\exp5_required_sections\input.json `
  --outdir out\exp5_required_sections_20260117
```

Expected outputs: `ucc_report.json`, `required_sections_checklist.md`, `audit_bundle.json`.

### Linux/macOS

```bash
. .venv/bin/activate
python -m ucc.cli run experiments/exp5_required_sections/module.yml --input experiments/exp5_required_sections/input.json --outdir out/exp5_required_sections_20260117
```

## Experiment 6: Compare Runs

### Windows (PowerShell)

```powershell
.\.venv\Scripts\python.exe -m ucc.cli run `
  experiments\exp6_compare_runs\module.yml `
  --input experiments\exp6_compare_runs\input.json `
  --outdir out\exp6_compare_runs_20260117
```

Expected outputs: `ucc_report.json`, `comparison.json`, `comparison.md`, `audit_bundle.json`.

### Linux/macOS

```bash
. .venv/bin/activate
python -m ucc.cli run experiments/exp6_compare_runs/module.yml --input experiments/exp6_compare_runs/input.json --outdir out/exp6_compare_runs_20260117
```
