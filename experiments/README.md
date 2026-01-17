# Experiments

## Lambda spike 2A (minimal)

```powershell
Set-Location "C:\Users\pdxvo\Documents\Lean\CoherenceLattice"

.\.venv\Scripts\python.exe -m ucc.cli run `
  experiments\lambda_spike_2a\module.yml `
  --input experiments\lambda_spike_2a\ucc_input.json `
  --outdir out\lambda_spike_2a_test
```
