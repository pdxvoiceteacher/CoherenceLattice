$ErrorActionPreference = "Stop"

if (!(Test-Path ".\lakefile.lean") -and !(Test-Path ".\lakefile.toml")) {
  throw "Run from repo root (where lakefile.lean lives)."
}

Write-Host "== Lean build: addons =="

lake build CoherenceLattice.Coherence.SacredGeometryAddons
lake build CoherenceLattice.Coherence.BetaRefutationAddons
lake build CoherenceLattice.Coherence.AddonTests
lake build CoherenceLattice.Coherence.PaperGlossAddons

Write-Host ""
Write-Host "OK: Lean addon targets build clean."