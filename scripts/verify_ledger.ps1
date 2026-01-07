$ErrorActionPreference = "Stop"
$REPO = (Resolve-Path "$PSScriptRoot\..").Path

$PY = Join-Path $REPO "tools\coherenceledger_bootstrap\.venv\Scripts\python.exe"
if (-not (Test-Path $PY)) { $PY = "python" }

& $PY -m coherenceledger verify --ledger (Join-Path $REPO "ledger.jsonl")
