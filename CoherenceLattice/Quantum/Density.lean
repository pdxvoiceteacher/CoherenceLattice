import Mathlib
import CoherenceLattice.Quantum.Pauli

namespace Coherence
namespace Quantum

open Complex Matrix

noncomputable section

/-- Squared magnitude proxy for ℂ as ℝ: re^2 + im^2. -/
def absSq (z : ℂ) : ℝ := z.re ^ 2 + z.im ^ 2

/-- Off-diagonal coherence proxy (basis-relative): absSq(ρ₀₁) + absSq(ρ₁₀). -/
def cohOffDiagSq (ρ : Mat2) : ℝ := absSq (ρ 0 1) + absSq (ρ 1 0)

/-- Coherence proxy is always nonnegative. -/
lemma cohOffDiagSq_nonneg (ρ : Mat2) : 0 ≤ cohOffDiagSq ρ := by
  unfold cohOffDiagSq absSq
  have h1 : 0 ≤ (ρ 0 1).re ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (ρ 0 1).im ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (ρ 1 0).re ^ 2 := sq_nonneg _
  have h4 : 0 ≤ (ρ 1 0).im ^ 2 := sq_nonneg _
  nlinarith

/-- A diagonal state in the computational basis has zero off-diagonal coherence proxy. -/
lemma cohOffDiagSq_of_diag (a b : ℂ) :
    cohOffDiagSq (fun i j =>
      if i = 0 ∧ j = 0 then a
      else if i = 1 ∧ j = 1 then b
      else 0) = 0 := by
  simp [cohOffDiagSq, absSq]

/-
Interpretation note (informal):
This coherence proxy is basis-relative. A basis change can move “coherence” between diagonal and off-diagonal entries.
-/

end  -- closes noncomputable section

end Quantum
end Coherence