import Mathlib
import CoherenceLattice.Coherence.PhyllotaxisDiskAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace PhyllotaxisDisk

noncomputable section

/-!
# PhyllotaxisDiskSuccessorAddons

Successor-specialized packing lemma: n and (n+1).

If N != 0 and n+1 <= N then:
- radius(n) <= radius(n+1)
- both points lie in the unit disk
-/

/-- Successor packing corollary (3 facts) for consecutive indices n and n+1. -/
theorem sunflower_packing_corollary_succ
    (n N : Nat) (hN0 : Ne N 0) (hn1N : n + 1 <= N) :
    And (radius n N <= radius (n + 1) N)
        (And ((px n N) ^ 2 + (py n N) ^ 2 <= 1)
             ((px (n + 1) N) ^ 2 + (py (n + 1) N) ^ 2 <= 1)) := by
  have h12 : n <= n + 1 := Nat.le_succ n
  have h1N : n <= N := Nat.le_trans h12 hn1N
  exact sunflower_packing_corollary3 n (n + 1) N hN0 h12 h1N hn1N

end
end PhyllotaxisDisk
end Coherence