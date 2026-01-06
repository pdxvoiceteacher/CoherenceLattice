import Mathlib
import CoherenceLattice.Coherence.PaperGlossAddons
import CoherenceLattice.Coherence.FlowerOfLifeAddons
import CoherenceLattice.Coherence.MusicRatioAddons
import CoherenceLattice.Coherence.SacredCirclesAddons
import CoherenceLattice.Coherence.TreeOfLifeAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence

noncomputable section

-- Keep a quick check that the paper-facing sunflower constructors still exist
example (n N : Nat) (hN0 : N = 0 -> False) (hn : n <= N) :
    (Coherence.PaperGloss.sunflowerPoint n N hN0 hn).x ^ 2
      + (Coherence.PaperGloss.sunflowerPoint n N hN0 hn).y ^ 2 <= 1 :=
  Coherence.PaperGloss.Lemma_SunflowerPointBound n N hN0 hn

-- Flower-of-Life count matches centered-hex
example (n : Nat) :
    Coherence.FlowerOfLife.flowerPoints n = Coherence.SacredGeometry.centeredHex n :=
  Coherence.FlowerOfLife.flowerPoints_eq_centeredHex n

-- Music ratios: a basic inequality
example : Coherence.MusicRatio.ratioMinorThird < Coherence.MusicRatio.ratioMajorThird :=
  Coherence.MusicRatio.ratioMinorThird_lt_majorThird

-- Sacred circles: circumference scaling
example (c : Coherence.SacredCircles.Circle) (k : Real) (hk : 0 <= k) :
    Coherence.SacredCircles.circumference (Coherence.SacredCircles.scale k hk c)
      = k * Coherence.SacredCircles.circumference c :=
  Coherence.SacredCircles.circumference_scale k hk c

-- Tree of Life -> coherence lattice: psi stays in [0,1]
example (s : Coherence.TreeOfLife.Sephira) :
    0 <= Coherence.TreeOfLife.sephiraPsi s ∧ Coherence.TreeOfLife.sephiraPsi s <= 1 :=
  Coherence.TreeOfLife.sephiraPsi_bounds s

end
end Coherence