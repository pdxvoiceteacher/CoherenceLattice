param(
  [string]$WorkflowPath = ".github/workflows/ci.yml",
  [int]$Perturbations = 3,
  [double]$MaxLambda = 0.01,
  [double]$MaxDeltaS = 0.01
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

if (!(Test-Path $WorkflowPath)) { Write-Host "Missing $WorkflowPath" -ForegroundColor Red; exit 1 }

$backup = "$WorkflowPath.bak_patchci_" + (Get-Date -Format "yyyyMMdd_HHmmss")
Copy-Item $WorkflowPath $backup -Force
Write-Host "Backup: $backup" -ForegroundColor Yellow

$lines = Get-Content $WorkflowPath
$out = New-Object System.Collections.Generic.List[string]

$nextRunIsSmoke = $false

foreach ($ln in $lines) {
  $line = $ln

  if ($line -like "*- name: Telemetry smoke (wrapper,*") {
    $nextRunIsSmoke = $true
    $out.Add($line)
    continue
  }

  if ($nextRunIsSmoke -and $line.TrimStart().StartsWith("run:")) {
    $indent = $line.Substring(0, $line.IndexOf("run:"))
    $out.Add($indent + "run: .venv/bin/python tools/telemetry/run_wrapper.py --out out/telemetry_smoke --quick --perturbations $Perturbations")
    $nextRunIsSmoke = $false
    continue
  }

  # Normalize validate thresholds if present
  if ($line -like "*tools/telemetry/validate_run.py*") {
    # Replace any existing max flags by removing them then appending correct ones
    $tmp = $line
    $tmp = $tmp -replace "--max-lambda\s+\S+", ""
    $tmp = $tmp -replace "--max-deltas\s+\S+", ""
    $tmp = ($tmp.TrimEnd() + " --max-lambda $MaxLambda --max-deltas $MaxDeltaS")
    $out.Add($tmp)
    continue
  }

  # sanitize any stray corrupted tokens
  if ($line -like "*run: .venv/bin/python $13*") {
    $indent = $line.Substring(0, $line.IndexOf("run:"))
    $out.Add($indent + "run: .venv/bin/python tools/telemetry/run_wrapper.py --out out/telemetry_smoke --quick --perturbations $Perturbations")
    continue
  }
  if ($line -like "*run: .venv/bin/python ${1}3*") {
    $indent = $line.Substring(0, $line.IndexOf("run:"))
    $out.Add($indent + "run: .venv/bin/python tools/telemetry/run_wrapper.py --out out/telemetry_smoke --quick --perturbations $Perturbations")
    continue
  }

  $out.Add($line)
}

$out | Out-File -FilePath $WorkflowPath -Encoding UTF8
Write-Host "patch_ci.ps1 applied safely." -ForegroundColor Green
