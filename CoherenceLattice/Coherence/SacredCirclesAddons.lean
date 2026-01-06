import Mathlib

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace SacredCircles

noncomputable section

/-!
# SacredCirclesAddons

Lightweight circle primitives usable for "sacred circles" / crop-circle pattern narration:

- Circle (center, radius>=0)
- circumference, area
- scaling (k>=0)
- a simple pattern container

No heavy Euclidean geometry; we keep it algebraic.
-/

structure Circle where
  cx : Real
  cy : Real
  r  : Real
  hr : 0 <= r

def circumference (c : Circle) : Real := (2 * Real.pi) * c.r
def area (c : Circle) : Real := Real.pi * (c.r ^ 2)

lemma circumference_nonneg (c : Circle) : 0 <= circumference c := by
  unfold circumference
  have hpi : 0 <= Real.pi := le_of_lt Real.pi_pos
  have h2 : 0 <= (2:Real) := by norm_num
  have hconst : 0 <= (2 * Real.pi) := mul_nonneg h2 hpi
  exact mul_nonneg hconst c.hr

lemma area_nonneg (c : Circle) : 0 <= area c := by
  unfold area
  have hpi : 0 <= Real.pi := le_of_lt Real.pi_pos
  have hr2 : 0 <= c.r ^ 2 := sq_nonneg c.r
  exact mul_nonneg hpi hr2

/-- Scale a circle by k>=0 (scales center and radius). -/
def scale (k : Real) (hk : 0 <= k) (c : Circle) : Circle :=
  { cx := k * c.cx
    cy := k * c.cy
    r  := k * c.r
    hr := mul_nonneg hk c.hr }

/-- Circumference scales linearly under k>=0. -/
lemma circumference_scale (k : Real) (hk : 0 <= k) (c : Circle) :
    circumference (scale k hk c) = k * circumference c := by
  unfold circumference scale
  ring

/-- Area scales quadratically under k>=0: area(k*c)=k^2*area(c). -/
lemma area_scale (k : Real) (hk : 0 <= k) (c : Circle) :
    area (scale k hk c) = (k ^ 2) * area c := by
  unfold area scale
  -- (k*r)^2 = k^2 * r^2
  simp [mul_pow, pow_two]
  ring

/-- A lightweight pattern container (e.g., crop-circle motif as a list of circles). -/
structure CirclePattern where
  circles : List Circle

def totalArea (p : CirclePattern) : Real :=
  p.circles.foldl (fun acc c => acc + area c) 0

end  -- noncomputable section
end SacredCircles
end Coherence