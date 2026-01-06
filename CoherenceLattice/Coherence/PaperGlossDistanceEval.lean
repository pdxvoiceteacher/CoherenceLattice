import Mathlib

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace PaperGlossDistanceEval

/-!
# PaperGlossDistanceEval

Float-only sanity output (NOT a theorem).
Prints a few successor distances for sunflower-style phyllotaxis:

distSuccF n N = sqrt((x(n+1)-x(n))^2 + (y(n+1)-y(n))^2)

This mirrors the narrative radial+angular law using Float approximations.
-/

-- Float approximations (stable for sanity checks)
def phiF : Float := 1.618033988749895
def piF  : Float := 3.141592653589793

def goldenTurnF : Float := 1.0 - (1.0 / phiF)
def goldenAngleRadF : Float := (2.0 * piF) * goldenTurnF

def radiusF (n N : Nat) : Float :=
  Float.sqrt ((Float.ofNat n) / (Float.ofNat N))

def thetaF (n : Nat) : Float :=
  (Float.ofNat n) * goldenAngleRadF

def pxF (n N : Nat) : Float :=
  radiusF n N * Float.cos (thetaF n)

def pyF (n N : Nat) : Float :=
  radiusF n N * Float.sin (thetaF n)

def distSqSuccF (n N : Nat) : Float :=
  let dx := pxF (n+1) N - pxF n N
  let dy := pyF (n+1) N - pyF n N
  dx*dx + dy*dy

def distSuccF (n N : Nat) : Float :=
  Float.sqrt (distSqSuccF n N)

/-- Choose a small N for quick sanity checks. -/
def N0 : Nat := 100

/-- A few n values to sample. -/
def ns : List Nat := [0,1,2,3,5,8,13,21,34,55,89]

/-- Table of (n, dist(n->n+1)). -/
def samples : List (Nat × Float) :=
  ns.map (fun n => (n, distSuccF n N0))

#eval samples

end PaperGlossDistanceEval
end Coherence