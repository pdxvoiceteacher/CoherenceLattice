import CoherenceLattice.Coherence.PaperGlossDistanceAddons
import Mathlib
import CoherenceLattice.Coherence.PhyllotaxisDiskAddons
import CoherenceLattice.Coherence.PhyllotaxisDiskSuccessorAddons
import CoherenceLattice.Coherence.PaperGlossSunflowerPointAddons
import CoherenceLattice.Coherence.PaperGlossPackingBundleAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace PaperGloss

noncomputable section

/-!
# PaperGlossAddons (surface)

Paper-facing definitions and successor lemma wrapper.
All public hypotheses are ASCII-safe: hN0 : (N = 0 -> False), ordering uses <=.
-/

/-- Inequality/corollary statement (Prop). -/
def CorollaryProp3 (n1 n2 N : Nat) : Prop :=
  And (Coherence.PhyllotaxisDisk.radius n1 N <= Coherence.PhyllotaxisDisk.radius n2 N)
      (And ((Coherence.PhyllotaxisDisk.px n1 N) ^ 2 + (Coherence.PhyllotaxisDisk.py n1 N) ^ 2 <= 1)
           ((Coherence.PhyllotaxisDisk.px n2 N) ^ 2 + (Coherence.PhyllotaxisDisk.py n2 N) ^ 2 <= 1))

/-- Bundle-extracted statement (Prop). -/
def BundleFacts3
    (n1 n2 N : Nat)
    (hN0 : N = 0 -> False)
    (h12 : n1 <= n2)
    (h1N : n1 <= N)
    (h2N : n2 <= N) : Prop :=
  let b := sunflowerPackingBundle n1 n2 N hN0 h12 h1N h2N
  And (b.p1.r <= b.p2.r)
      (And (b.p1.x ^ 2 + b.p1.y ^ 2 <= 1)
           (b.p2.x ^ 2 + b.p2.y ^ 2 <= 1))

/-- Proof of the inequality/corollary statement. -/
theorem Corollary_SunflowerPacking3
    (n1 n2 N : Nat)
    (hN0 : N = 0 -> False)
    (h12 : n1 <= n2)
    (h1N : n1 <= N)
    (h2N : n2 <= N) :
    CorollaryProp3 n1 n2 N := by
  have hN0' : Ne N 0 := by
    intro h
    exact hN0 h
  exact Coherence.PhyllotaxisDisk.sunflower_packing_corollary3 n1 n2 N hN0' h12 h1N h2N

/-- Successor-specialized PaperGloss wrapper: n and (n+1). -/
theorem Corollary_SunflowerPackingSucc
    (n N : Nat) (hN0 : N = 0 -> False) (hn1N : n + 1 <= N) :
    CorollaryProp3 n (n + 1) N := by
  have hN0' : Ne N 0 := by
    intro h
    exact hN0 h
  -- Use the disk successor lemma and rewrite into CorollaryProp3
  have hs :=
    Coherence.PhyllotaxisDisk.sunflower_packing_corollary_succ n N hN0' hn1N
  simpa [CorollaryProp3] using hs

end
end PaperGloss
end Coherence