import Mathlib
import CoherenceLattice.Coherence.PhyllotaxisDiskAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PaperGloss

noncomputable section

/-!
# PaperGlossAddons

Paper-facing lemma names for manuscript citation (no new theory).
-/

/-- (Paper Corollary) Monotone spiral radius + unit-disk bound (sunflower packing). -/
theorem Corollary_SunflowerPacking (n1 n2 N : Nat) (hN0 : N = 0 -> False)
    (h12 : n1 <= n2) (h2N : n2 <= N) :
    And (Coherence.PhyllotaxisDisk.radius n1 N <= Coherence.PhyllotaxisDisk.radius n2 N)
        ((Coherence.PhyllotaxisDisk.px n2 N) ^ 2 + (Coherence.PhyllotaxisDisk.py n2 N) ^ 2 <= 1) := by
  have hN0' : N ≠ 0 := by
    intro h
    exact hN0 h
  exact Coherence.PhyllotaxisDisk.sunflower_packing_corollary n1 n2 N hN0' h12 h2N

end
end PaperGloss
end Coherence