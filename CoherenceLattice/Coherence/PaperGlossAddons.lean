import Mathlib
import CoherenceLattice.Coherence.SacredGeometryAddons
import CoherenceLattice.Coherence.BetaRefutationAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace PaperGloss

noncomputable section

/-!
# PaperGlossAddons

Paper-facing lemma names for the addon modules so the manuscript can cite stable identifiers.
No new theory: just curated wrappers.
-/

/-- (Paper Lemma) Golden ratio identity: phi^2 = phi + 1. -/
theorem Lemma_PhiSquared :
    Coherence.SacredGeometry.phi * Coherence.SacredGeometry.phi
      = Coherence.SacredGeometry.phi + 1 :=
  Coherence.SacredGeometry.phi_sq

/-- (Paper Lemma) Centered hex number at n=2 is 19 (Flower-of-Life ring count sanity). -/
theorem Lemma_CenteredHex_2 :
    Coherence.SacredGeometry.centeredHex 2 = 19 := by
  simpa using Coherence.SacredGeometry.centeredHex_2

/-- (Paper Theorem) No fixed exponent b satisfies M = I^b for both example systems. -/
theorem Theorem_NoFixedExponentExample :
    ¬ ∃ b : ℝ,
        Coherence.BetaRefutation.systemHigh.M =
          Coherence.BetaRefutation.systemHigh.I ^ b ∧
        Coherence.BetaRefutation.systemLow.M =
          Coherence.BetaRefutation.systemLow.I ^ b :=
  Coherence.BetaRefutation.no_fixed_b_example

end  -- closes noncomputable section
end PaperGloss
end Coherence