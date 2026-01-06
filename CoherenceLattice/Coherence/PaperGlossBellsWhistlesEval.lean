import Mathlib

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace PaperGlossBellsWhistlesEval

/-!
# PaperGlossBellsWhistlesEval

Float-only sanity output (NOT a theorem; NOT imported by core proofs).

Prints:
- golden angle (deg + rad)
- row samples: n, r, theta, x, y, dx, dy, distNext
- CSV #1: same columns
- CSV #2: adds xNext,yNext (for Python verification of both generator + distance)
-/

def phiF : Float := 1.618033988749895
def piF  : Float := 3.141592653589793

def goldenTurnF : Float := 1.0 - (1.0 / phiF)
def goldenAngleRadF : Float := (2.0 * piF) * goldenTurnF
def goldenAngleDegF : Float := 360.0 * goldenTurnF

def radiusF (n N : Nat) : Float :=
  Float.sqrt ((Float.ofNat n) / (Float.ofNat N))

def thetaF (n : Nat) : Float :=
  (Float.ofNat n) * goldenAngleRadF

def pxF (n N : Nat) : Float :=
  radiusF n N * Float.cos (thetaF n)

def pyF (n N : Nat) : Float :=
  radiusF n N * Float.sin (thetaF n)

def dxSuccF (n N : Nat) : Float := pxF (n+1) N - pxF n N
def dySuccF (n N : Nat) : Float := pyF (n+1) N - pyF n N

def distSqSuccF (n N : Nat) : Float :=
  let dx := dxSuccF n N
  let dy := dySuccF n N
  dx*dx + dy*dy

def distSuccF (n N : Nat) : Float :=
  Float.sqrt (distSqSuccF n N)

structure Row where
  n : Nat
  r : Float
  theta : Float
  x : Float
  y : Float
  dx : Float
  dy : Float
  distNext : Float
deriving Repr

def row (n N : Nat) : Row :=
  { n := n
    r := radiusF n N
    theta := thetaF n
    x := pxF n N
    y := pyF n N
    dx := dxSuccF n N
    dy := dySuccF n N
    distNext := distSuccF n N }

def N0 : Nat := 100
def ns : List Nat := [0,1,2,3,5,8,13,21,34,55,89]
def rows : List Row := ns.map (fun n => row n N0)

-- CSV #1 (same as rows)
def csv1Header : String := "n,r,theta,x,y,dx,dy,distNext"
def csv1Line (rw : Row) : String :=
  s!"{rw.n},{rw.r},{rw.theta},{rw.x},{rw.y},{rw.dx},{rw.dy},{rw.distNext}"
def csv1 : String :=
  String.intercalate "\n" (csv1Header :: (rows.map csv1Line))

-- CSV #2 (adds next point)
def csv2Header : String := "n,r,theta,x,y,xNext,yNext,dx,dy,distNext"
def csv2Line (rw : Row) : String :=
  let xN := pxF (rw.n + 1) N0
  let yN := pyF (rw.n + 1) N0
  s!"{rw.n},{rw.r},{rw.theta},{rw.x},{rw.y},{xN},{yN},{rw.dx},{rw.dy},{rw.distNext}"
def csv2 : String :=
  String.intercalate "\n" (csv2Header :: (rows.map csv2Line))

#eval (goldenAngleDegF, goldenAngleRadF)
#eval rows
#eval csv1
#eval csv2

end PaperGlossBellsWhistlesEval
end Coherence