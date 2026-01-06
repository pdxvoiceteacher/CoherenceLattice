import Mathlib
import CoherenceLattice.Coherence.TreeOfLifeAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace TreeOfLifeGraph

noncomputable section

open Coherence.TreeOfLife

/-!
# TreeOfLifeGraphAddons

Adjacency graph over Sephirot + psi-path projection.

Fix for this snapshot:
`List.Forall` over `map` reduces to a composed predicate:
  List.Forall p (map f tl)  ~>  List.Forall (p ∘ f) tl
So we convert the IH using `simpa [psiPath]`.
-/

def adj : Sephira -> List Sephira
  | .keter     => [.chokmah, .binah]
  | .chokmah   => [.keter, .chesed, .binah]
  | .binah     => [.keter, .gevurah, .chokmah]
  | .chesed    => [.chokmah, .tiphereth]
  | .gevurah   => [.binah, .tiphereth]
  | .tiphereth => [.chesed, .gevurah, .netzach, .hod, .yesod]
  | .netzach   => [.tiphereth, .yesod]
  | .hod       => [.tiphereth, .yesod]
  | .yesod     => [.netzach, .hod, .malkuth, .tiphereth]
  | .malkuth   => [.yesod]

def validStep (a b : Sephira) : Prop := b ∈ adj a

def validPath : List Sephira -> Prop
  | [] => True
  | [_] => True
  | a :: b :: tl => validStep a b ∧ validPath (b :: tl)

def psiPath (xs : List Sephira) : List Real :=
  xs.map sephiraPsi

def psiBound (x : Real) : Prop := And (0 <= x) (x <= 1)

/-- Every psi in psiPath lies in [0,1]. -/
theorem psiPath_bounds (xs : List Sephira) :
    List.Forall psiBound (psiPath xs) := by
  induction xs with
  | nil =>
      simp [psiPath, psiBound]
  | cons s tl ih =>
      have hs : psiBound (sephiraPsi s) := by
        simpa [psiBound] using sephiraPsi_bounds s
      have ih' : List.Forall (psiBound ∘ sephiraPsi) tl := by
        -- ih : List.Forall psiBound (psiPath tl) = List.Forall psiBound (map sephiraPsi tl)
        simpa [psiPath] using ih
      -- Goal reduces to hs ∧ ih' after simp [psiPath]
      simpa [psiPath] using And.intro hs ih'

end
end TreeOfLifeGraph
end Coherence