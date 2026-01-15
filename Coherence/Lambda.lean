import Mathlib

set_option linter.style.commandStart false
noncomputable section

namespace Coherence

/-- Mean of a list (0 on empty). -/
def listMean (xs : List ℝ) : ℝ :=
  match xs with
  | [] => 0
  | _  => xs.sum / (xs.length : ℝ)

/-- Variance of a list (0 on empty). -/
def listVar (xs : List ℝ) : ℝ :=
  match xs with
  | [] => 0
  | _  =>
    let μ := listMean xs
    (xs.map (fun x => (x - μ)^2)).sum / (xs.length : ℝ)

/-- Toy Λ: variance normalized by a baseline variance. -/
def lambdaIndex (xs : List ℝ) (baseVar : ℝ) : ℝ :=
  if baseVar = 0 then 0 else listVar xs / baseVar

/-- Optional: clamped Λ into [0,1] (always bounded). -/
def lambda01 (xs : List ℝ) (baseVar : ℝ) : ℝ :=
  max 0 (min 1 (lambdaIndex xs baseVar))

/-- For any μ, the sum of squared deviations is ≥ 0. -/
theorem sum_sq_nonneg (μ : ℝ) (xs : List ℝ) :
    0 ≤ (xs.map (fun x => (x - μ)^2)).sum := by
  induction xs with
  | nil =>
      simp
  | cons a xs ih =>
      simp [List.sum_cons, ih, add_nonneg, sq_nonneg]

/-- Variance is always nonnegative. -/
theorem listVar_nonneg (xs : List ℝ) : 0 ≤ listVar xs := by
  cases xs with
  | nil =>
      simp [listVar]
  | cons a xs =>
      have hnum :
          0 ≤ ((a :: xs).map (fun x => (x - (listMean (a :: xs)))^2)).sum := by
        simpa using sum_sq_nonneg (listMean (a :: xs)) (a :: xs)
      have hlen : 0 < ((List.length (a :: xs)) : ℝ) := by
        exact_mod_cast Nat.zero_lt_succ _
      have : 0 ≤
          ((a :: xs).map (fun x => (x - (listMean (a :: xs)))^2)).sum / (List.length (a :: xs) : ℝ) := by
        exact div_nonneg hnum (le_of_lt hlen)
      simpa [listVar, listMean] using this

/-- If baseline variance is positive, lambdaIndex is nonnegative. -/
theorem lambdaIndex_nonneg (xs : List ℝ) (baseVar : ℝ) (hpos : 0 < baseVar) :
    0 ≤ lambdaIndex xs baseVar := by
  unfold lambdaIndex
  by_cases hb : baseVar = 0
  · simp [hb]
  · have : 0 ≤ listVar xs / baseVar := by
      exact div_nonneg (listVar_nonneg xs) (le_of_lt hpos)
    simp [hb, this]

/-- If baseline variance bounds the variance from above (and is positive), then lambdaIndex ≤ 1. -/
theorem lambdaIndex_le_one_of_le (xs : List ℝ) (baseVar : ℝ)
    (hpos : 0 < baseVar) (hle : listVar xs ≤ baseVar) :
    lambdaIndex xs baseVar ≤ 1 := by
  unfold lambdaIndex
  by_cases hb : baseVar = 0
  · have h : (0 : ℝ) < 0 := by simpa [hb] using hpos
    exact False.elim ((lt_irrefl 0) h)
  · have hbne : baseVar ≠ 0 := hb
    -- Multiply inequality by inv(baseVar) ≥ 0
    have hinv_nonneg : 0 ≤ baseVar⁻¹ := le_of_lt (inv_pos.2 hpos)
    have hmul : listVar xs * baseVar⁻¹ ≤ baseVar * baseVar⁻¹ := by
      exact mul_le_mul_of_nonneg_right hle hinv_nonneg
    -- Rewrite division as multiplication by inverse, and baseVar*inv = 1
    have hdiv1 : listVar xs / baseVar ≤ 1 := by
      -- listVar/baseVar = listVar * baseVar⁻¹
      -- baseVar * baseVar⁻¹ = 1 (since baseVar ≠ 0)
      simpa [div_eq_mul_inv, hbne, mul_inv_cancel, mul_assoc] using hmul
    simp [hb, hdiv1]

/-- lambda01 is always in [0,1] (unconditional boundedness). -/
theorem lambda01_bounds (xs : List ℝ) (baseVar : ℝ) :
    0 ≤ lambda01 xs baseVar ∧ lambda01 xs baseVar ≤ 1 := by
  unfold lambda01
  constructor
  · exact le_max_left _ _
  ·
    have hmin : min 1 (lambdaIndex xs baseVar) ≤ 1 := by
      exact min_le_left _ _
    exact max_le (by linarith) hmin

end Coherence
