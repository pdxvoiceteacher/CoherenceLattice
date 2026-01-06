import Mathlib
import CoherenceLattice.Coherence.PaperGlossAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence

noncomputable section

-- Def-only typecheck: distance proxy exists and is a Real
example (n N : Nat) (hN0 : N = 0 -> False) (hn1N : n + 1 <= N) : Real :=
  Coherence.PaperGloss.dist_succ n N hN0 hn1N

end
end Coherence