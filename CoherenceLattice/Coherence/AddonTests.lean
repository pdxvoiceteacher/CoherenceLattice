import Mathlib
import CoherenceLattice.Coherence.PaperGlossAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence

noncomputable section

-- Successor lemma compiles: n and n+1
example (n N : Nat) (hN0 : N = 0 -> False) (hn1N : n + 1 <= N) :
    Coherence.PaperGloss.CorollaryProp3 n (n + 1) N :=
  Coherence.PaperGloss.Corollary_SunflowerPackingSucc n N hN0 hn1N

end
end Coherence