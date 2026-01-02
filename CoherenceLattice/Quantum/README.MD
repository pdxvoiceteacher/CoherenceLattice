# Quantum Anchor Pack (Qubit / Finite-Dimensional)

This folder provides an **orthodox qubit (2-level) anchor** intended for reviewer verification:
Pauli matrices, commutators, explicit eigenstates/normalization, and a two-level canonical ensemble
partition function with a Gibbs normalization proof.

**No new physics claims.**  
These files do not modify Schrödinger dynamics, measurement postulates, or QFT. They provide a
finite-dimensional “physics anchor slice” that can be mapped into the broader coherence-lattice/UCC
governance framework.

## Key theorems (Lean names to cite)

### Pauli commutators
- `Coherence.Quantum.comm_sigmaX_sigmaY`
- `Coherence.Quantum.comm_sigmaY_sigmaZ`
- `Coherence.Quantum.comm_sigmaZ_sigmaX`

### Eigenstate + normalization anchors
- `Coherence.Quantum.σz_mul_ket0`
- `Coherence.Quantum.σz_mul_ket1`
- `Coherence.Quantum.norm_ket0`
- `Coherence.Quantum.norm_ket1`
- `Coherence.Quantum.orth_ket0_ket1`

(Planned next: σx eigenstates |±⟩ and normalization.)

### Two-level thermal / partition function
- `Coherence.Quantum.Z_closed`
- `Coherence.Quantum.trace_rho`

Interpretation note (for paper/README): off-diagonal magnitude depends on basis; a basis change can move coherence from off-diagonal to diagonal. This is the standard “coherence is basis-relative” fact — our proxy demonstrates that without claiming any new QM.
## Snapshot-robust choices (mathlib compatibility)

Some mathlib snapshots vary in which convenience lemmas/names are available. To keep this repo build-stable across snapshots, we intentionally use:

- **`absSq z = z.re^2 + z.im^2`** as a magnitude proxy in `Density.lean` instead of `Complex.abs`. This avoids dependency on a particular `Complex.abs` API surface while still providing a basis-relative “off-diagonal coherence” proxy.

- **Algebraic partition-function analysis** in `ThermoExtras.lean` instead of a calculus proof of `⟨H⟩ = −∂β log Z`. The expected-energy identity is derived directly from Gibbs weights (still standard statistical mechanics), which avoids requiring specific derivative simp-lemmas that may differ across snapshots.
