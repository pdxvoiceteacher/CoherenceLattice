param(
  [string]$WorkflowPath = ".github/workflows/ci.yml",
  [double]$MaxLambda = 0.01,
  [double]$MaxDeltaS = 0.01,
  [int]$Perturbations = 3
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

function Ok($m){ Write-Host $m -ForegroundColor Green }
function Warn($m){ Write-Host $m -ForegroundColor Yellow }
function Fail($m){ Write-Host $m -ForegroundColor Red; exit 1 }

if (!(Test-Path $WorkflowPath)) { Fail "Missing CI workflow: $WorkflowPath" }

$backup = "$WorkflowPath.bak_" + (Get-Date -Format "yyyyMMdd_HHmmss")
Copy-Item $WorkflowPath $backup -Force
Ok "Backup: $backup"

$text = Get-Content $WorkflowPath -Raw

# --- 1) Ensure telemetry smoke uses perturbations=N ---
$text = $text -replace '(tools/telemetry/run_wrapper\.py\b[^\r\n]*--perturbations\s+)\d+', ('$1' + $Perturbations)

# If the run_wrapper call exists but has no --perturbations, append it.
if ($text -match 'tools/telemetry/run_wrapper\.py' -and $text -notmatch '--perturbations') {
  $text = $text -replace '(tools/telemetry/run_wrapper\.py\b[^\r\n]*)', ('$1 --perturbations ' + $Perturbations)
  Ok "Added --perturbations $Perturbations to telemetry smoke."
}

# --- 2) Ensure validate telemetry has max-lambda/max-deltas with our values ---
# Replace existing values if present
$text = $text -replace '--max-lambda\s+\S+', ('--max-lambda ' + $MaxLambda)
$text = $text -replace '--max-deltas\s+\S+', ('--max-deltas ' + $MaxDeltaS)

# If validate_run line exists but lacks max flags, append them.
if ($text -match 'tools/telemetry/validate_run\.py' -and $text -notmatch '--max-lambda') {
  $text = $text -replace '(tools/telemetry/validate_run\.py\b[^\r\n]*)', ('$1 --max-lambda ' + $MaxLambda + ' --max-deltas ' + $MaxDeltaS)
  Ok "Appended --max-lambda/--max-deltas to validate telemetry."
}

# --- 3) Insert Plasticity v1 steps after Validate control decision schema (idempotent) ---
$proposalBlock = @"
      - name: Enforce policy gate (Es->Lambda->T)
        run: .venv/bin/python tools/telemetry/enforce_policy_gate.py --decision out/telemetry_smoke/control_decision.json --allow-slow

      - name: Emit change proposal (proposal-only)
        run: .venv/bin/python tools/telemetry/propose_change.py --run-dir out/telemetry_smoke --telemetry out/telemetry_smoke/telemetry.json --state out/telemetry_smoke/state_estimate.json --decision out/telemetry_smoke/control_decision.json --out out/telemetry_smoke/change_proposal.json

      - name: Validate change proposal schema
        run: .venv/bin/python tools/telemetry/validate_proposal.py out/telemetry_smoke/change_proposal.json

"@

if ($text -match 'Enforce policy gate \(Es->Lambda->T\)') {
  Ok "Plasticity v1 steps already present; skipping insert."
} else {
  $lines = $text -split "`n"
  $out = New-Object System.Collections.Generic.List[string]
  $inserted = $false

  for ($i=0; $i -lt $lines.Count; $i++) {
    $out.Add($lines[$i])

    if (-not $inserted -and $lines[$i] -match '^\s*-\s+name:\s+Validate control decision schema\s*$') {
      # copy lines until blank line ends that step
      $i++
      while ($i -lt $lines.Count) {
        $out.Add($lines[$i])
        if ($lines[$i].Trim() -eq "") { break }
        $i++
      }
      foreach ($l in ($proposalBlock -split "`r?`n")) { $out.Add($l) }
      $inserted = $true
    }
  }

  if ($inserted) {
    $text = ($out -join "`n")
    Ok "Inserted Plasticity v1 (policy gate + proposal) steps."
  } else {
    Warn "Could not find 'Validate control decision schema' step; Plasticity v1 steps NOT inserted."
    Warn "If your CI uses different step names, paste the telemetry section and we retarget the patch."
  }
}

# Write back
$text | Out-File -FilePath $WorkflowPath -Encoding UTF8
Ok "Patched: $WorkflowPath"
Ok "Done."
