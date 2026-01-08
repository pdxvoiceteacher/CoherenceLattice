param(
  [Parameter(Mandatory=$true)][string]$VoteDir,
  [string]$ProverManifest = "prover_manifest.json",
  [string]$SnarkjsBin = $env:UCC_SNARKJS_BIN
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

if (-not $SnarkjsBin) { $SnarkjsBin = "snarkjs" }

$VoteDir = (Resolve-Path $VoteDir).Path
$pmPath = Join-Path $VoteDir $ProverManifest
if (-not (Test-Path $pmPath)) { throw "Missing prover manifest: $pmPath" }

$pm = Get-Content $pmPath -Raw | ConvertFrom-Json

function R([string]$p) {
  if (-not $p) { return $null }
  if ([System.IO.Path]::IsPathRooted($p)) { return $p }
  return (Join-Path $VoteDir $p)
}

$mode = $pm.backend.mode
$alg  = $pm.backend.alg.ToLower()

$wasm   = R $pm.artifacts.wasm_path
$zkey   = R $pm.artifacts.zkey_path
$input  = R $pm.artifacts.input_json_path
$wtns   = R $pm.artifacts.witness_path
$proof  = R $pm.artifacts.proof_json_path
$public = R $pm.artifacts.public_json_path

New-Item -ItemType Directory -Force -Path ([System.IO.Path]::GetDirectoryName($proof)) | Out-Null
New-Item -ItemType Directory -Force -Path ([System.IO.Path]::GetDirectoryName($public)) | Out-Null

if ($mode -eq "fullprover") {
  if (-not (Test-Path $input)) { throw "Missing input_json_path: $input" }
  if (-not (Test-Path $wasm))  { throw "Missing wasm_path: $wasm" }
  if (-not (Test-Path $zkey))  { throw "Missing zkey_path: $zkey" }
  & $SnarkjsBin $alg fullprover $input $wasm $zkey $proof $public
}
elseif ($mode -eq "prove") {
  if (-not (Test-Path $wtns)) { throw "Missing witness_path: $wtns" }
  if (-not (Test-Path $zkey)) { throw "Missing zkey_path: $zkey" }
  & $SnarkjsBin $alg prove $zkey $wtns $proof $public
}
else {
  throw "Unsupported mode: $mode"
}

Write-Host "Wrote proof:  $proof"
Write-Host "Wrote public: $public"
