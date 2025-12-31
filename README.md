# Coherence Lattice (Lean 4 + mathlib)

This repository contains a Lean 4 formalization of a “coherence lattice” model:
- A coherence **state** is (E, T) ∈ [0,1]×[0,1]
- A coherence score **Ψ** is defined as Ψ(E,T) = E*T
- States are mapped into discrete **regimes** S0..S4 via Ψ bands
- A regime **adjacency graph** constrains allowed transitions
- ΔSyn-inspired dynamics (`stepPsi`, `stepET`) are proven to respect the regime graph (“no teleport”)

## Quickstart (build locally)

From the repository root:

```powershell
lake exe cache get
lake build
Where the “paper claims” live
Paper-facing theorem wrappers (stable citation names) are in:

CoherenceLattice/Coherence/NarrativeGloss.lean

Key results you can cite directly:

Coherence.PaperGloss.Lemma_DrivePositive

Coherence.PaperGloss.Lemma_BoundedDrift_stepET

Coherence.PaperGloss.Lemma_PsiNondecreasing_stepET

Coherence.PaperGloss.Theorem_NoTeleport

Coherence.PaperGloss.Theorem_DeltaSynPsiStep_Safe

Coherence.PaperGloss.Theorem_DeltaSynETStep_Safe

Coherence.PaperGloss.Corollary_TrajectoryET_ValidPath

How to review
Start here:

paper/REPRODUCE.md — exact steps to build + verify the main claims

paper/theorem-map.md — informal claims ↔ Lean theorem names ↔ files

Repo layout (high-level)
CoherenceLattice/Coherence/Basic.lean — baseline Ψ, ΔSyn input + lemmas

CoherenceLattice/Coherence/Lattice.lean — unit-square state model and Ψ properties

CoherenceLattice/Coherence/Regime.lean — regimes + adjacency graph + path validity

CoherenceLattice/Coherence/Classifier.lean — regime classification by Ψ bands

CoherenceLattice/Coherence/NoTeleport.lean — |ΔΨ| < τ0 ⇒ valid regime transition

CoherenceLattice/Coherence/Dynamics.lean — ΔSyn ψ-step (stepPsi) + safety theorem

CoherenceLattice/Coherence/DynamicsET.lean — ΔSyn E/T-step (stepET) + safety theorem

CoherenceLattice/Coherence/Interpretation.lean — interpretation lemmas

CoherenceLattice/Coherence/NarrativeGloss.lean — wrapper theorem names for citation

Contributing / Issues
PRs are welcome. Please keep lake build green.
