**https://www.linkedin.com/pulse/coherence-lattice-framework-cross-domain-evidence-oelyc**
---

## Build status

<!-- Replace <OWNER>/<REPO> and workflow filenames if needed -->
**Lean proofs:**  
[![Lean proofs](https://github.com/pdxvoiceteacher/CoherenceLattice/actions/workflows/lean_proofs_ci.yml/badge.svg?branch=master)](https://github.com/pdxvoiceteacher/CoherenceLattice/actions/workflows/lean_proofs_ci.yml?query=branch%3Amaster)


## CoherenceLattice — GUFT / Coherence / Sacred Geometry / Generative Engines (Lean + Python)

This repository is a working lab for cross-domain coherence modeling and formal verification (Lean 4 + Mathlib) alongside Python engines (UCC + coherence/music utilities). The goal is a unified, testable interface for reasoning about coherence, coarse-graining, safety transitions, and generative mappings (including sacred geometry and musical ratio systems), with paper-facing “gloss” layers and reproducible artifacts.

**Status: ✅ Everything referenced below is building green under Lean 4.27.0-rc1.**

## Repo Structure (high level)

CoherenceLattice/Coherence/
Lean modules for coherence lattice, ΔSyn dynamics guardrails, paper-facing wrappers, sacred geometry formalizations, and eval-only diagnostics.

CoherenceLattice/Quantum/
Lean quantum anchor demonstrations (Pauli matrices, simple finite constructions).

ucc/
Universal Control Codex (Python) — governance & safety tooling + CI-style checks and demos.

python/
Python coherence simulations / music experiments / supporting utilities.

paper/
Manuscript support files and exported CSV artifacts (paper/out/*.csv).

Lean: Core Coherence Lattice (formal)
Coherence state + invariants

State: points (E,T) in the unit square [0,1]×[0,1]

Coherence: psi = E*T

# Proofs include:

psi_nonneg and psi_le_one → 0 ≤ psi ≤ 1

monotonicity lemmas and Lipschitz-style bounds in the unit square

Regimes + safe transitions (“no teleport”)

classify : State -> Regime maps a state to discrete bands using thresholds tau0..tau3

validTransition enforces adjacency-only regime steps

No-teleport theorem: if |Δpsi| < tau0 then the induced regime transition is valid

This is used to prove that capped ΔSyn-driven updates cannot “jump regimes” unexpectedly.

ΔSyn dynamics guardrails (formal)

Two safe update styles are formalized:

ψ-centric step (stepPsi) — update psi directly, then clamp back into [0,1]

E/T-centric step (stepET) — update E and T independently, clamp each into [0,1]


**Key theorems:**

validTransition_stepPsi / validTransition_stepET
Each step respects the regime graph.

abs_psi_stepET_sub_le
Per-step bounded drift: |Δpsi| ≤ tau0/2

interpretation lemma variants linking ΔS sign to monotone drift (paper-friendly wrapper names live in PaperGloss).

Paper-facing wrapper layer

A “gloss” layer provides stable lemma names and narrative-friendly constructors so a manuscript can cite Lean without exposing internal file structure.


**This includes:**

stable lemma wrappers

sunflower packing bundle constructors

successor-specialized corollaries


**Lean: Sacred Geometry Formalizations (formal + scaffolds)**
Flower of Life / centered hex counts (formal)

A Flower-of-Life / hex-lattice point count model using centered hex numbers:

recursive flowerPoints and proof that:

flowerPoints n = centeredHex n

Sacred circles + crop-circle scaffolding (formal + validation)


**Algebraic circle primitives:**

circle structure with radius nonneg proof

circumference + area

scaling laws: circumference scales linearly, area scales quadratically (k ≥ 0)

**Crop-circle pattern scaffolding:**

rosette circle generation via List.range k

count lemmas (rosette length; rosette+center count = k+1)

signature structure (order,count) + validation lemma


**Lean: Tree of Life → Coherence Lattice mapping (synced)**

We model the Tree of Life (Sephirot) as a mapping into the coherence lattice state space:

EFrac / TFrac provide a single source of truth as unit fractions (Nat/Nat with proofs).

sephiraState derives the lattice state (E,T) from these fractions.

sephiraPsi is coherence psi on the sephiraState.

proof:

sephiraPsi_bounds : 0 ≤ sephiraPsi s ∧ sephiraPsi s ≤ 1

A lightweight adjacency graph over Sephirot is included (TreeOfLifeGraphAddons) with psiPath + bounds over paths.


**Lean: Music — ratios + scale scaffolds (synced profiles)**
Just ratios (formal, Lean-light)

canonical ratios: unison, minor third, major third, fourth, fifth, octave

ordering / chain lemmas usable in narrative

Music scale scaffold (profiles)

The repo now has synced consonance profiles stored in MusicScaleScaffoldAddons.lean:

Rat profiles (computable / eval tooling)

consonantSetRat_major

consonantSetRat_minor

chordOKRat_major, chordOKRat_minor

Real profiles (proof-facing scaffolds)

consonantSet_major

consonantSet_minor

chordOK_major, chordOK_minor

This ensures the eval artifacts and proof-facing scaffolds can’t drift out of sync.

Eval-only Artifacts (“bells & whistles”)

Eval-only files are non-proof diagnostics intended for:

quick sanity checks

generating CSV outputs for Python diffs

reproducible paper artifacts


**Crop circles: rotated centers + invariance checks**

CropCircleRotatedCentersEval.lean

outputs CSV rows for each rotation angle:

rotated centers

distance-from-origin invariance

per-angle summary row

global summary row

strict CSV column completion (okAngle column always present)

comment separators # ---- next angle ---- for readability


**Tree of Life: band table CSV**

TreeOfLifeBandCSV.lean

prints:

name, E, T, psi, band

band thresholds are configurable in the file

exportable to paper/out/tree_of_life_bands.csv


**Tree of Life: Real/Float spot checks**

TreeOfLifeRealFloatEval.lean

prints exact Rat psi and Float psi

uses #reduce on Real psi terms for structural sanity (no execution)


**Music: profile comparison CSVs**

MusicScaffoldEval.lean

prints scale + chord accept/reject tables under:

major consonance profile

minor-friendly consonance profile

includes per-profile __SUMMARY__ rows

Exporting CSV Artifacts to paper/out
One-shot export (Tree of Life, Crop circles, Music)


## Use the PowerShell export script shared in chat to generate:

paper/out/tree_of_life_bands.csv

paper/out/crop_circle_rotated_centers.csv

paper/out/music_scaffold_profiles.csv (combined sections)

Split music export

The “split by section markers” PowerShell script outputs:

paper/out/music_scale.csv

paper/out/music_chords_major.csv

paper/out/music_chords_minor.csv

Building / Running Lean
Build individual modules
lake build CoherenceLattice.Coherence.TreeOfLifeAddons
lake build CoherenceLattice.Coherence.TreeOfLifeGraphAddons
lake build CoherenceLattice.Coherence.CropCirclesAddons
lake build CoherenceLattice.Coherence.MusicScaleScaffoldAddons

Run eval-only tools
lake env lean CoherenceLattice/Coherence/CropCircleRotatedCentersEval.lean
lake env lean CoherenceLattice/Coherence/TreeOfLifeBandCSV.lean
lake env lean CoherenceLattice/Coherence/MusicScaffoldEval.lean

Building / Running Python (UCC + engines)

Python components live primarily under:

ucc/ (Universal Control Codex)

python/src/ (coherence sim + coherence music experiments)

# Typical workflow:

set up venv

run tests and example demos

compare outputs against exported Lean CSVs when relevant (e.g., music ratios / phyllotaxis / crop circles)

(If you want, we can add a dedicated python/tools/compare_csv.py to diff Lean-exported CSVs vs Python engine output.)

# Notes on Encoding + Windows

The project uses UTF-8 (no BOM) for Lean files generated via PowerShell.

ASCII-safe identifiers are used where Windows encoding pitfalls have previously caused “unexpected token” errors.

# Contributing / Workflow

Make a change in Lean or Python

lake build the relevant modules

Run eval artifacts when appropriate and export to paper/out

Commit Lean + exported CSV artifacts together when they substantively update the paper-facing story

## License / Attribution

This repo includes original work by UVLM/Prislac and collaborators, plus dependencies from Mathlib and standard toolchains.

---

## Quickstart (Windows + PowerShell)

This is the fastest “clone → build → run eval tools → export CSVs” path on Windows.

0) Prereqs

You’ll need:

Git

Lean toolchain via elan (recommended)

Lake (comes with Lean via elan)

A working C toolchain isn’t typically needed for Mathlib-only Lean builds, but keep your environment consistent with what you already use (you’re on Lean 4.27.0-rc1).

1) Clone + enter repo
git clone https://github.com/pdxvoiceteacher/CoherenceLattice.git
cd CoherenceLattice

2) Confirm Lean + Lake
lean --version
lake --version

3) Pull dependencies (Mathlib, etc.)
lake update

4) Build the core Lean project

Full build:

lake build


Or build key targets (faster, iterative):

lake build CoherenceLattice.Coherence.TreeOfLifeAddons
lake build CoherenceLattice.Coherence.TreeOfLifeGraphAddons
lake build CoherenceLattice.Coherence.CropCirclesAddons
lake build CoherenceLattice.Coherence.MusicScaleScaffoldAddons

5) Run eval-only tools (prints CSV/text to console)
lake env lean CoherenceLattice/Coherence/TreeOfLifeBandCSV.lean
lake env lean CoherenceLattice/Coherence/CropCircleRotatedCentersEval.lean
lake env lean CoherenceLattice/Coherence/MusicScaffoldEval.lean

6) Export eval outputs to paper/out/ (UTF-8 no BOM)

Create output directory:

New-Item -ItemType Directory -Force -Path paper\out | Out-Null


Export Tree of Life band table:

$enc = New-Object System.Text.UTF8Encoding($false)
$tol = (lake env lean CoherenceLattice/Coherence/TreeOfLifeBandCSV.lean) -join "`n"
$tol = ($tol -split "`n" | Where-Object { $_ -notmatch '^\s*#' -and $_ -ne "" }) -join "`n"
[System.IO.File]::WriteAllText("paper\out\tree_of_life_bands.csv", $tol, $enc)
"wrote paper\out\tree_of_life_bands.csv"


Export crop-circle rotated centers (filters # comment separators):

$crop = (lake env lean CoherenceLattice/Coherence/CropCircleRotatedCentersEval.lean) -join "`n"
$crop = ($crop -split "`n" | Where-Object { $_ -notmatch '^\s*#' -and $_ -ne "" }) -join "`n"
[System.IO.File]::WriteAllText("paper\out\crop_circle_rotated_centers.csv", $crop, $enc)
"wrote paper\out\crop_circle_rotated_centers.csv"


Export combined music scaffold output (keeps # section markers):

$music = (lake env lean CoherenceLattice/Coherence/MusicScaffoldEval.lean) -join "`n"
[System.IO.File]::WriteAllText("paper\out\music_scaffold_profiles.csv", $music, $enc)
"wrote paper\out\music_scaffold_profiles.csv"

7) Optional: Split music into three CSVs

If you’ve added the section-splitting PowerShell script from chat, run it to generate:

paper/out/music_scale.csv

paper/out/music_chords_major.csv

paper/out/music_chords_minor.csv

8) Commit + push
git status
git add CoherenceLattice/Coherence/*.lean paper/out/*.csv
git commit -m "Add Lean proofs + eval CSV artifacts (Tree-of-Life, crop circles, music profiles)"
git push
