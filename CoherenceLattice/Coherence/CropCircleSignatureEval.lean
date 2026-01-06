import Mathlib

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace CropCircleSignatureEval

/-!
# CropCircleSignatureEval

Float-only CSV output for signature-style validation:
order,count,totalArea

totalArea is approximate:
  pi*rCenter^2 + k*pi*rRing^2
-/

def piF : Float := 3.141592653589793

def areaF (r : Float) : Float := piF * (r*r)

def totalAreaF (k : Nat) (rCenter rRing : Float) : Float :=
  areaF rCenter + (Float.ofNat k) * areaF rRing

def csvHeader : String := "k,order,count,rCenter,rRing,totalArea"
def csvLine (k : Nat) (rCenter rRing : Float) : String :=
  let order := k
  let count := k + 1
  let a := totalAreaF k rCenter rRing
  s!"{k},{order},{count},{rCenter},{rRing},{a}"

def emitCSV : IO Unit := do
  let k0 : Nat := 12
  let rC : Float := 0.3
  let rR : Float := 0.2
  IO.println csvHeader
  IO.println (csvLine k0 rC rR)
  -- a couple more sample orders
  IO.println (csvLine 6 rC rR)
  IO.println (csvLine 24 rC rR)

#eval emitCSV

end CropCircleSignatureEval
end Coherence