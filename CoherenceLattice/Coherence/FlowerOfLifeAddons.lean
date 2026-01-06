import Mathlib
import CoherenceLattice.Coherence.SacredGeometryAddons
import CoherenceLattice.Coherence.SacredGeometryLemmasAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace FlowerOfLife

/-!
# FlowerOfLifeAddons

We model a Flower-of-Life / hex-lattice point count via centered-hex numbers.

flowerPoints(0) = 1
flowerPoints(n+1) = flowerPoints(n) + 6*(n+1)

Then flowerPoints n = centeredHex n.
-/

def ringPoints : Nat -> Nat
| 0 => 1
| (n+1) => 6 * (n+1)

def flowerPoints : Nat -> Nat
| 0 => 1
| (n+1) => flowerPoints n + 6 * (n+1)

lemma ringPoints_succ (n : Nat) : ringPoints (n+1) = 6 * (n+1) := by
  simp [ringPoints]

lemma flowerPoints_succ (n : Nat) : flowerPoints (n+1) = flowerPoints n + 6 * (n+1) := by
  simp [flowerPoints]

theorem flowerPoints_eq_centeredHex (n : Nat) :
    flowerPoints n = Coherence.SacredGeometry.centeredHex n := by
  induction n with
  | zero =>
      simp [flowerPoints, Coherence.SacredGeometry.centeredHex]
  | succ n ih =>
      have hch :
          Coherence.SacredGeometry.centeredHex (n+1)
            = Coherence.SacredGeometry.centeredHex n + 6 * (n+1) :=
        Coherence.SacredGeometryLemmas.centeredHex_succ n
      calc
        flowerPoints (n+1)
            = flowerPoints n + 6 * (n+1) := by simp [flowerPoints]
        _ = Coherence.SacredGeometry.centeredHex n + 6 * (n+1) := by simpa [ih]
        _ = Coherence.SacredGeometry.centeredHex (n+1) := by simpa using hch.symm

end FlowerOfLife
end Coherence