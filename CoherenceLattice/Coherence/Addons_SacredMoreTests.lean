import Mathlib
import CoherenceLattice.Coherence.CropCirclesAddons
import CoherenceLattice.Coherence.TreeOfLifeGraphAddons
import CoherenceLattice.Coherence.FlowerOfLifeAddons
import CoherenceLattice.Coherence.MusicRatioAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence

noncomputable section

-- Flower-of-Life count matches centeredHex
example (n : Nat) :
    Coherence.FlowerOfLife.flowerPoints n = Coherence.SacredGeometry.centeredHex n :=
  Coherence.FlowerOfLife.flowerPoints_eq_centeredHex n

-- A music inequality
example : Coherence.MusicRatio.ratioMinorThird < Coherence.MusicRatio.ratioMajorThird :=
  Coherence.MusicRatio.ratioMinorThird_lt_majorThird

-- Crop circles: rosette length lemma
example (k : Nat) (R r : Real) (hr : 0 <= r) :
    (Coherence.CropCircles.rosetteCircles k R r hr).length = k :=
  Coherence.CropCircles.rosetteCircles_length k R r hr

-- Tree of Life psiPath bounds
example (xs : List Coherence.TreeOfLife.Sephira) :
    List.Forall (fun x => 0 <= x ∧ x <= 1) (Coherence.TreeOfLifeGraph.psiPath xs) :=
  Coherence.TreeOfLifeGraph.psiPath_bounds xs

end
end Coherence