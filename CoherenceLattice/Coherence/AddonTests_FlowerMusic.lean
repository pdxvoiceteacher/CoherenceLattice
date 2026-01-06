import Mathlib
import CoherenceLattice.Coherence.FlowerOfLifeAddons
import CoherenceLattice.Coherence.MusicRatioAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence

noncomputable section

example (n : Nat) :
    Coherence.FlowerOfLife.flowerPoints n = Coherence.SacredGeometry.centeredHex n :=
  Coherence.FlowerOfLife.flowerPoints_eq_centeredHex n

example : Coherence.MusicRatio.ratioMinorThird < Coherence.MusicRatio.ratioMajorThird :=
  Coherence.MusicRatio.ratioMinorThird_lt_majorThird

end
end Coherence