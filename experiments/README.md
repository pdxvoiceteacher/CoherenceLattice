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
