# Universal Control Codex (UCC) — v0.1 scaffold

This folder provides a minimal, safe-by-default scaffold for UCC modules:

- Modules are defined in YAML and validated against a JSON Schema.
- A small step-runner executes only built-in step types (no arbitrary eval).
- Every run emits an **audit bundle** containing hashes of the module, inputs, and outputs.

## Quickstart (use existing repo venv)

From repo root:

```powershell
.\python\.venv\Scripts\python.exe -m pip install -e .\ucc[dev]
ucc validate ucc\modules\tches_lambda_tag.yml
ucc run ucc\modules\tches_lambda_tag.yml --input ucc\tasks\tches_series_example.json --outdir ucc\out\demo_run
Outputs:

ucc/out/demo_run/report.json

ucc/out/demo_run/audit_bundle.json

Safety note

Do not run untrusted modules. This runner intentionally supports a limited set of built-in step types.
