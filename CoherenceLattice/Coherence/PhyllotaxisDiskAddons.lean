import Mathlib
import CoherenceLattice.Coherence.PhyllotaxisDegreesAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PhyllotaxisDisk

noncomputable section

open Coherence.PhyllotaxisDegrees

def theta (n : Nat) : Real :=
  (n : Real) * goldenAngleRad

def radius (n N : Nat) : Real :=
  Real.sqrt ((n : Real) / (N : Real))

def px (n N : Nat) : Real :=
  radius n N * Real.cos (theta n)

def py (n N : Nat) : Real :=
  radius n N * Real.sin (theta n)

/-- Radius monotonicity: if n1 <= n2 and N != 0 then radius n1 N <= radius n2 N. -/
lemma radius_mono_of_le (n1 n2 N : Nat) (hN0 : N ≠ 0) (h12 : n1 <= n2) :
    radius n1 N <= radius n2 N := by
  have hNpos : 0 < (N : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero hN0)
  have h12R : (n1 : Real) <= (n2 : Real) := by
    exact_mod_cast h12
  have hdiv : (n1 : Real) / (N : Real) <= (n2 : Real) / (N : Real) := by
    exact div_le_div_of_nonneg_right h12R (le_of_lt hNpos)
  unfold radius
  exact Real.sqrt_le_sqrt hdiv

lemma normSq_eq_radiusSq (n N : Nat) :
    (px n N) ^ 2 + (py n N) ^ 2 = (radius n N) ^ 2 := by
  set r : Real := radius n N with hr
  set t : Real := theta n with ht
  have htrig : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
    simpa using Real.cos_sq_add_sin_sq t
  have hpx : px n N = r * Real.cos t := by
    simp [px, hr, ht]
  have hpy : py n N = r * Real.sin t := by
    simp [py, hr, ht]
  calc
    (px n N) ^ 2 + (py n N) ^ 2
        = (r * Real.cos t) ^ 2 + (r * Real.sin t) ^ 2 := by simpa [hpx, hpy]
    _ = (r ^ 2) * (Real.cos t ^ 2) + (r ^ 2) * (Real.sin t ^ 2) := by
          simp [mul_pow]
    _ = (r ^ 2) * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
    _ = r ^ 2 := by simpa [htrig]
    _ = (radius n N) ^ 2 := by simpa [hr]

lemma normSq_le_one_of_le (n N : Nat) (hN0 : N ≠ 0) (hn : n <= N) :
    (px n N) ^ 2 + (py n N) ^ 2 <= 1 := by
  have hnorm : (px n N) ^ 2 + (py n N) ^ 2 = (radius n N) ^ 2 :=
    normSq_eq_radiusSq n N

  have hNpos : 0 < (N : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero hN0)

  have hnR : (n : Real) <= (N : Real) := by
    exact_mod_cast hn

  let u : Real := (n : Real) / (N : Real)

  have hu0 : 0 <= u := by
    have : 0 <= (n : Real) := by exact_mod_cast (Nat.zero_le n)
    exact div_nonneg this (le_of_lt hNpos)

  have hu1 : u <= 1 := by
    have hdiv : (n : Real) / (N : Real) <= (N : Real) / (N : Real) := by
      exact div_le_div_of_nonneg_right hnR (le_of_lt hNpos)
    have hN0R : (N : Real) ≠ 0 := by exact ne_of_gt hNpos
    simpa [u, hN0R] using hdiv

  have hr2 : (radius n N) ^ 2 = u := by
    have : radius n N = Real.sqrt u := by
      simp [radius, u]
    simp [this, pow_two, Real.mul_self_sqrt hu0]

  calc
    (px n N) ^ 2 + (py n N) ^ 2
        = (radius n N) ^ 2 := by simpa [hnorm]
    _ = u := by simpa [hr2]
    _ <= 1 := hu1

/--
Combined corollary for “sunflower packing” narration:

If N != 0 and n1 <= n2 <= N, then:
  (1) radius(n1) <= radius(n2)   (monotone spiral radius)
  (2) x(n2)^2 + y(n2)^2 <= 1     (later point is inside the unit disk)
-/
lemma sunflower_packing_corollary (n1 n2 N : Nat) (hN0 : N ≠ 0)
    (h12 : n1 <= n2) (h2N : n2 <= N) :
    And (radius n1 N <= radius n2 N)
        ((px n2 N) ^ 2 + (py n2 N) ^ 2 <= 1) := by
  refine And.intro (radius_mono_of_le n1 n2 N hN0 h12) ?_
  exact normSq_le_one_of_le n2 N hN0 h2N

end
end PhyllotaxisDisk
end Coherence