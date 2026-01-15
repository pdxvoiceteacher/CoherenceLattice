import CoherenceLattice.Coherence.Lambda

set_option linter.style.commandStart false
noncomputable section

namespace Coherence

/-- A simple decision mode used for governance gating. -/
inductive DecisionMode where
  | proceed
  | slow
  | review
  | refuse
  deriving DecidableEq, Repr

/-- Governance threshold for Λ (warning region). -/
def lambdaWarn : ℝ := 0.80

/-- A policy: if Λ is high, we must not proceed without escalation. -/
def lambdaGate (lam : ℝ) : DecisionMode :=
  if lam ≥ lambdaWarn then DecisionMode.review else DecisionMode.proceed

/-- Theorem: if Λ is in the warning region, the gate returns review. -/
theorem lambdaGate_triggers_review (lam : ℝ) (h : lam ≥ lambdaWarn) :
    lambdaGate lam = DecisionMode.review := by
  unfold lambdaGate
  simp [h]

/-- Theorem: if Λ is below warning, the gate returns proceed. -/
theorem lambdaGate_allows_proceed (lam : ℝ) (h : lam < lambdaWarn) :
    lambdaGate lam = DecisionMode.proceed := by
  unfold lambdaGate
  have : ¬ (lam ≥ lambdaWarn) := by linarith
  simp [this]

end Coherence
