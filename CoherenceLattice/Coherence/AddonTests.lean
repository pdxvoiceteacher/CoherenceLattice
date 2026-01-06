import Mathlib
import CoherenceLattice.Coherence.PaperGlossAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence

noncomputable section

example (n1 n2 N : Nat) (hN0 : N = 0 -> False) (h12 : n1 <= n2) (h2N : n2 <= N) :
    And (Coherence.PhyllotaxisDisk.radius n1 N <= Coherence.PhyllotaxisDisk.radius n2 N)
        ((Coherence.PhyllotaxisDisk.px n2 N) ^ 2 + (Coherence.PhyllotaxisDisk.py n2 N) ^ 2 <= 1) :=
  Coherence.PaperGloss.Corollary_SunflowerPacking n1 n2 N hN0 h12 h2N

end
end Coherence