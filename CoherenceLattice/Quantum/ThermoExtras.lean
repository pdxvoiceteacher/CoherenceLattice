import Mathlib

namespace Coherence
namespace Quantum

open Real

noncomputable section

/-- Convenience: x = βΔ/2. -/
def x (β Δ : ℝ) : ℝ := β * Δ / 2

/-- Two-level partition function: Z = exp(-x) + exp(x). -/
def Z_real (β Δ : ℝ) : ℝ := Real.exp (-(x β Δ)) + Real.exp (x β Δ)

/-- Gibbs weight for +Δ/2 level. -/
def p_plus (β Δ : ℝ) : ℝ := Real.exp (-(x β Δ)) / Z_real β Δ

/-- Gibbs weight for -Δ/2 level. -/
def p_minus (β Δ : ℝ) : ℝ := Real.exp (x β Δ) / Z_real β Δ

/-- Expected energy from Gibbs weights for energies ±Δ/2. -/
def E_from_probs (β Δ : ℝ) : ℝ :=
  (Δ / 2) * p_plus β Δ + (-Δ / 2) * p_minus β Δ

/-- Closed-form expected energy (same denominator Z). -/
def E_expected (β Δ : ℝ) : ℝ :=
  (Δ / 2) * (Real.exp (-(x β Δ)) - Real.exp (x β Δ)) / Z_real β Δ

/-- Algebraic identity: E_from_probs = E_expected (no calculus needed). -/
lemma E_from_probs_eq_E_expected (β Δ : ℝ) :
    E_from_probs β Δ = E_expected β Δ := by
  unfold E_from_probs E_expected p_plus p_minus Z_real x
  -- push multiplications through division so we can combine over a common denominator
  simp [mul_div_assoc, add_div, sub_eq_add_neg, mul_add, add_mul]
  ring

/-
Informal (standard) physics note:
For Z = exp(-x) + exp(x), one also has ⟨H⟩ = -(d/dβ) log Z and ⟨H⟩ = -(Δ/2) * tanh(x).
We keep the Lean formalization algebraic here to remain robust across mathlib snapshots.
-/

end  -- closes noncomputable section

end Quantum
end Coherence