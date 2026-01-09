param(
  [string]$ZipPath = "C:\Users\pdxvo\Documents\Lean\CoherenceLattice\uvlm_upload_bundle.zip"
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repo = (Resolve-Path "$PSScriptRoot\..").Path
Set-Location $repo

# Collect targets (array of strings)
$targets = @(
  ".github\workflows\ci.yml",
  "scripts\dev_bootstrap.ps1",
  "scripts\dev_bootstrap.py",
  "scripts\patch_ci.ps1",
  "scripts\new_receipt.ps1",
  "scripts\ingest_proposal.ps1",
  "scripts\approve_proposal.ps1",
  "scripts\make_uvlm_bundle.ps1",

  "schema\telemetry",
  "schema\governance",

  "tools\telemetry",
  "tools\validate_governance.py",
  "tools\validate_json.py",

  "tests\baselines",

  "governance\proposals",
  "governance\implementation",

  "notes"
)

# Keep only existing paths
$existing = @()
foreach ($t in $targets) {
  if (Test-Path $t) { $existing += $t }
}

# Manifest
New-Item -Force -ItemType Directory .\out\uvlm_bundle_tmp | Out-Null
@"
UVLM Upload Bundle Manifest
==========================

Repo: https://github.com/pdxvoiceteacher/CoherenceLattice

Purpose:
- Fast onboarding for Echo iterations
- Reproducible green (tests + CI)
- Telemetry cognition loop (telemetry -> state_estimate -> policy -> proposal)
- Plasticity governance (approved proposals + receipts + rollback)

Key commands (Windows):
  powershell -ExecutionPolicy Bypass -File scripts\dev_bootstrap.ps1
  powershell -ExecutionPolicy Bypass -File scripts\patch_ci.ps1
  powershell -ExecutionPolicy Bypass -File scripts\new_receipt.ps1
  powershell -ExecutionPolicy Bypass -File scripts\make_uvlm_bundle.ps1

"@ | Set-Content .\out\uvlm_bundle_tmp\UVLM_FOLDER_MANIFEST.md -Encoding UTF8

$manifest = ".\out\uvlm_bundle_tmp\UVLM_FOLDER_MANIFEST.md"

Write-Host "Including paths:" -ForegroundColor Cyan
$existing | ForEach-Object { Write-Host " - $_" }

# Build zip
Remove-Item $ZipPath -ErrorAction SilentlyContinue

# IMPORTANT: pass paths as an array (no comma expression)
$all = @()
$all += $existing
$all += $manifest

Compress-Archive -Path $all -DestinationPath $ZipPath -Force

# Cleanup
Remove-Item -Recurse -Force .\out\uvlm_bundle_tmp -ErrorAction SilentlyContinue

Write-Host "Created bundle: $ZipPath" -ForegroundColor Green
Write-Host "REMINDER: upload this zip to the UVLM GPT project folder after core changes." -ForegroundColor Yellow
explorer /select,"$ZipPath"
