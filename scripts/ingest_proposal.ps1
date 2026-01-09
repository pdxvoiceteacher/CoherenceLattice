param(
  [Parameter(Mandatory=$true)][string]$ProposalPath,
  [ValidateSet("queue","approved","rejected")][string]$Status="queue",
  [string]$Note=""
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repo = (Resolve-Path "$PSScriptRoot\..").Path
Set-Location $repo

$PY = ".\.venv\Scripts\python.exe"
if (!(Test-Path $PY)) { Write-Host "Missing venv python: $PY" -ForegroundColor Red; exit 1 }

if (!(Test-Path $ProposalPath)) { Write-Host "Missing proposal file: $ProposalPath" -ForegroundColor Red; exit 1 }

New-Item -Force -ItemType Directory .\governance\proposals\queue | Out-Null
New-Item -Force -ItemType Directory .\governance\proposals\approved | Out-Null
New-Item -Force -ItemType Directory .\governance\proposals\rejected | Out-Null

& $PY .\tools\telemetry\proposal_queue.py ingest --proposal $ProposalPath --status $Status --note $Note

git status
Write-Host "Ingest complete. Commit this proposal file and (optionally) open a PR for promotion workflow." -ForegroundColor Yellow
