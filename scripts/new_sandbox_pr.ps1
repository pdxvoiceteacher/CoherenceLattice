param(
  [string]$ApprovedProposalFile = "",
  [switch]$NoSmoke,
  [int]$Perturbations = 3,
  [string]$BranchPrefix = "auto/impl",
  [string]$BaseBranch = "master",
  [switch]$NoOpenBrowser
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

function Normalize-GitHubUrl([string]$u) {
  if ($u -match '^git@github\.com:(.+?)(\.git)?$') { return "https://github.com/$($Matches[1])" }
  if ($u -match '^https://github\.com/(.+?)(\.git)?$') { return "https://github.com/$($Matches[1])" }
  return ""
}

$repo = (Resolve-Path "$PSScriptRoot\..").Path
Set-Location $repo

$PY = ".\.venv\Scripts\python.exe"
if (!(Test-Path $PY)) {
  Write-Host "Missing venv python: $PY" -ForegroundColor Yellow
  Write-Host "Attempting bootstrap (scripts/dev_bootstrap.py --skip-tests)..." -ForegroundColor Yellow
  if (Test-Path ".\scripts\dev_bootstrap.py") {
    python .\scripts\dev_bootstrap.py --skip-tests
  }
}

if (!(Test-Path $PY)) {
  Write-Host "Still missing venv python. Run dev bootstrap first." -ForegroundColor Red
  exit 1
}

# Auto-select newest approved proposal if not provided
$approvedDir = ".\governance\proposals\approved"
New-Item -Force -ItemType Directory $approvedDir | Out-Null

if ([string]::IsNullOrWhiteSpace($ApprovedProposalFile)) {
  $latest = Get-ChildItem -Path $approvedDir -Filter *.json -File |
            Sort-Object LastWriteTime -Descending |
            Select-Object -First 1
  if ($null -eq $latest) {
    Write-Host "No approved proposal found in $approvedDir" -ForegroundColor Red
    exit 1
  }
  $ApprovedProposalFile = $latest.FullName
  Write-Host "Auto-selected approved proposal:" -ForegroundColor Cyan
  Write-Host "  $ApprovedProposalFile" -ForegroundColor Cyan
} else {
  if (!(Test-Path $ApprovedProposalFile)) {
    Write-Host "Missing approved proposal: $ApprovedProposalFile" -ForegroundColor Red
    exit 1
  }
  $ApprovedProposalFile = (Resolve-Path $ApprovedProposalFile).Path
  Write-Host "Using approved proposal:" -ForegroundColor Cyan
  Write-Host "  $ApprovedProposalFile" -ForegroundColor Cyan
}

# Derive proposal id from filename: YYYY...__<id>__...
$fname = [System.IO.Path]::GetFileName($ApprovedProposalFile)
$proposalId = ""
if ($fname -like "*__*__*") {
  $proposalId = ($fname.Split("__"))[1]
} else {
  $proposalId = $fname.Replace(".json","")
}

$stamp = (Get-Date).ToUniversalTime().ToString("yyyyMMdd_HHmmssZ")
$branch = "$BranchPrefix`_$stamp`_$proposalId"

Write-Host "Creating branch: $branch" -ForegroundColor Green
git checkout -b $branch | Out-Null

if (-not $NoSmoke) {
  Write-Host "Running telemetry smoke + perturbations..." -ForegroundColor Cyan
  Remove-Item -Recurse -Force .\out\telemetry_smoke -ErrorAction SilentlyContinue

  & $PY .\tools\telemetry\run_wrapper.py --out .\out\telemetry_smoke --quick --perturbations $Perturbations
  & $PY .\tools\telemetry\validate_run.py .\out\telemetry_smoke\telemetry.json --min-psi 0.80 --min-t 0.80 --min-es 0.80 --max-lambda 0.01 --max-deltas 0.01 --warn-only

  & $PY .\tools\telemetry\state_estimator.py --telemetry .\out\telemetry_smoke\telemetry.json --perturbations .\out\telemetry_smoke\perturbations.json --history .\out\history\state_history.jsonl --window 50 --alpha 0.70 --out .\out\telemetry_smoke\state_estimate.json
  & $PY .\tools\telemetry\validate_state.py .\out\telemetry_smoke\state_estimate.json

  & $PY .\tools\telemetry\policy.py --state .\out\telemetry_smoke\state_estimate.json --out .\out\telemetry_smoke\control_decision.json
  & $PY .\tools\telemetry\validate_decision.py .\out\telemetry_smoke\control_decision.json

  & $PY .\tools\telemetry\propose_change.py --run-dir .\out\telemetry_smoke --telemetry .\out\telemetry_smoke\telemetry.json --state .\out\telemetry_smoke\state_estimate.json --decision .\out\telemetry_smoke\control_decision.json --out .\out\telemetry_smoke\change_proposal.json
  & $PY .\tools\telemetry\validate_proposal.py .\out\telemetry_smoke\change_proposal.json
} else {
  Write-Host "Skipping smoke run (NoSmoke set)." -ForegroundColor Yellow
}

Write-Host "Generating receipt + rollback (Plasticity v3)..." -ForegroundColor Cyan
powershell -ExecutionPolicy Bypass -File .\scripts\new_receipt.ps1 -ApprovedProposalFile $ApprovedProposalFile -RunDir .\out\telemetry_smoke

Write-Host "Validating receipt + rollback..." -ForegroundColor Cyan
& $PY .\tools\telemetry\validate_receipt.py .\governance\implementation\receipts\*.json
& $PY .\tools\telemetry\validate_rollback.py .\governance\implementation\rollback\*.json

git add governance\implementation | Out-Null
git commit -m "Plasticity v4: sandbox PR scaffold (receipt+rollback) for proposal $proposalId" | Out-Null

git push -u origin $branch

# --- v4.1: Print + open PR URL ---
$origin = (git remote get-url origin) 2>$null
$repoUrl = Normalize-GitHubUrl $origin

if ($repoUrl) {
  $prUrl = "$repoUrl/compare/$BaseBranch...$branch?expand=1"
  Write-Host "`nPR URL (auto-generated):" -ForegroundColor Green
  Write-Host "  $prUrl" -ForegroundColor Green
  if (-not $NoOpenBrowser) {
    Start-Process $prUrl | Out-Null
  }
} else {
  Write-Host "`nCould not derive GitHub URL from origin: $origin" -ForegroundColor Yellow
  Write-Host "Open PR manually from branch: $branch" -ForegroundColor Yellow
}

Write-Host "`nDONE." -ForegroundColor Green
Write-Host "Reminder: after major changes, run scripts/make_uvlm_bundle.ps1 and upload zip to GPT project folder." -ForegroundColor Yellow
