import Mathlib
import CoherenceLattice.Coherence.PaperGlossSunflowerPointAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace PaperGloss

noncomputable section

/-!
# PaperGlossDistanceAddons

Def-only distance proxy between successive sunflowerPolarPoint n and (n+1).
This is intended for narrative and later Python-engine validation, not proof.
All public hypotheses are ASCII-safe.
-/

/-- Convenience: derive hn : n <= N from hn1N : n+1 <= N. -/
def le_of_succ_le {n N : Nat} (hn1N : n + 1 <= N) : n <= N :=
  Nat.le_trans (Nat.le_succ n) hn1N

/-- Successor polar point at index n (requires n+1 <= N so we can derive n <= N). -/
def polarPoint_n (n N : Nat) (hN0 : N = 0 -> False) (hn1N : n + 1 <= N) : SunflowerPolarPoint :=
  sunflowerPolarPoint n N hN0 (le_of_succ_le hn1N)

/-- Successor polar point at index n+1. -/
def polarPoint_succ (n N : Nat) (hN0 : N = 0 -> False) (hn1N : n + 1 <= N) : SunflowerPolarPoint :=
  sunflowerPolarPoint (n + 1) N hN0 hn1N

/-- Delta-x between successive points: x(n+1) - x(n). -/
def deltaX_succ (n N : Nat) (hN0 : N = 0 -> False) (hn1N : n + 1 <= N) : Real :=
  (polarPoint_succ n N hN0 hn1N).x - (polarPoint_n n N hN0 hn1N).x

/-- Delta-y between successive points: y(n+1) - y(n). -/
def deltaY_succ (n N : Nat) (hN0 : N = 0 -> False) (hn1N : n + 1 <= N) : Real :=
  (polarPoint_succ n N hN0 hn1N).y - (polarPoint_n n N hN0 hn1N).y

/-- Squared distance proxy: dx^2 + dy^2 (avoids sqrt for some downstream uses). -/
def distSq_succ (n N : Nat) (hN0 : N = 0 -> False) (hn1N : n + 1 <= N) : Real :=
  (deltaX_succ n N hN0 hn1N) ^ 2 + (deltaY_succ n N hN0 hn1N) ^ 2

/-- Euclidean distance proxy: sqrt(dx^2 + dy^2). -/
def dist_succ (n N : Nat) (hN0 : N = 0 -> False) (hn1N : n + 1 <= N) : Real :=
  Real.sqrt (distSq_succ n N hN0 hn1N)

end
end PaperGloss
end Coherence