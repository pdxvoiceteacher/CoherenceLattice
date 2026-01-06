import Mathlib
import CoherenceLattice.Coherence.SacredCirclesAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace CropCircles

noncomputable section

/-!
# CropCirclesAddons

Lean-light crop-circle / sacred-circle scaffolding.
Avoids Mathlib `_root_.Circle` ambiguity via SCircle alias.
Includes symmetry-signature validation lemma(s).
-/

abbrev SCircle := Coherence.SacredCircles.Circle
abbrev Pattern := Coherence.SacredCircles.CirclePattern

def rotPoint (theta : Real) (p : Real × Real) : Real × Real :=
  (p.1 * Real.cos theta - p.2 * Real.sin theta,
   p.1 * Real.sin theta + p.2 * Real.cos theta)

def translateCircle (dx dy : Real) (c : SCircle) : SCircle :=
  { cx := c.cx + dx
    cy := c.cy + dy
    r  := c.r
    hr := c.hr }

def rotateCircle (theta : Real) (c : SCircle) : SCircle :=
  let p := rotPoint theta (c.cx, c.cy)
  { cx := p.1
    cy := p.2
    r  := c.r
    hr := c.hr }

def originCircle (r : Real) (hr : 0 <= r) : SCircle :=
  { cx := 0, cy := 0, r := r, hr := hr }

/-- Pattern transforms (definition-only). -/
def rotatePattern (theta : Real) (p : Pattern) : Pattern :=
  { circles := p.circles.map (rotateCircle theta) }

def translatePattern (dx dy : Real) (p : Pattern) : Pattern :=
  { circles := p.circles.map (translateCircle dx dy) }

lemma rotatePattern_count (theta : Real) (p : Pattern) :
    (rotatePattern theta p).circles.length = p.circles.length := by
  simp [rotatePattern]

lemma translatePattern_count (dx dy : Real) (p : Pattern) :
    (translatePattern dx dy p).circles.length = p.circles.length := by
  simp [translatePattern]

def angleStep (k : Nat) : Real :=
  (2 * Real.pi) / (k : Real)

def rosetteCircles (k : Nat) (R r : Real) (hr : 0 <= r) : List SCircle :=
  (List.range k).map (fun i =>
    { cx := R * Real.cos ((i : Real) * angleStep k)
      cy := R * Real.sin ((i : Real) * angleStep k)
      r  := r
      hr := hr })

lemma rosetteCircles_length (k : Nat) (R r : Real) (hr : 0 <= r) :
    (rosetteCircles k R r hr).length = k := by
  simp [rosetteCircles]

def motifRosetteWithCenter (k : Nat) (R rCenter rRing : Real)
    (hCenter : 0 <= rCenter) (hRing : 0 <= rRing) : Pattern :=
  { circles := (originCircle rCenter hCenter) :: (rosetteCircles k R rRing hRing) }

lemma motifRosetteWithCenter_count (k : Nat) (R rCenter rRing : Real)
    (hCenter : 0 <= rCenter) (hRing : 0 <= rRing) :
    (motifRosetteWithCenter k R rCenter rRing hCenter hRing).circles.length = k + 1 := by
  simp [motifRosetteWithCenter, rosetteCircles_length, originCircle]

structure SymmetrySignature where
  order : Nat
  count : Nat
deriving Repr

def signatureRosetteWithCenter (k : Nat) (R rCenter rRing : Real)
    (hCenter : 0 <= rCenter) (hRing : 0 <= rRing) : SymmetrySignature :=
  { order := k
    count := (motifRosetteWithCenter k R rCenter rRing hCenter hRing).circles.length }

lemma signatureRosetteWithCenter_order (k : Nat) (R rCenter rRing : Real)
    (hCenter : 0 <= rCenter) (hRing : 0 <= rRing) :
    (signatureRosetteWithCenter k R rCenter rRing hCenter hRing).order = k := by
  rfl

lemma signatureRosetteWithCenter_count (k : Nat) (R rCenter rRing : Real)
    (hCenter : 0 <= rCenter) (hRing : 0 <= rRing) :
    (signatureRosetteWithCenter k R rCenter rRing hCenter hRing).count = k + 1 := by
  simp [signatureRosetteWithCenter, motifRosetteWithCenter_count]

/-- Symmetry signature validation (order + count) for rosette-with-center. -/
theorem signatureRosetteWithCenter_valid (k : Nat) (R rCenter rRing : Real)
    (hCenter : 0 <= rCenter) (hRing : 0 <= rRing) :
    And ((signatureRosetteWithCenter k R rCenter rRing hCenter hRing).order = k)
        ((signatureRosetteWithCenter k R rCenter rRing hCenter hRing).count = k + 1) :=
  And.intro
    (signatureRosetteWithCenter_order k R rCenter rRing hCenter hRing)
    (signatureRosetteWithCenter_count k R rCenter rRing hCenter hRing)

end
end CropCircles
end Coherence