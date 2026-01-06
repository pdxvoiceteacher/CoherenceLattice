import Mathlib
import CoherenceLattice.Coherence.Lattice

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace TreeOfLife

noncomputable section

open Coherence.Lattice

/-!
# TreeOfLifeAddons

A formal "Tree of Life" node type (Sephira) mapped to the coherence lattice State (E,T) in [0,1]^2.

This is a *mapping layer* (data + basic bounds), not a claim of physics.
-/

inductive Sephira
  | keter | chokmah | binah | chesed | gevurah | tiphereth | netzach | hod | yesod | malkuth
deriving DecidableEq, Repr

def mkUnit01 (x : Real) (h0 : 0 <= x) (h1 : x <= 1) : Coherence.Lattice.Unit01 :=
  ⟨x, ⟨h0, h1⟩⟩

def mkState (E T : Real)
    (hE0 : 0 <= E) (hE1 : E <= 1)
    (hT0 : 0 <= T) (hT1 : T <= 1) : Coherence.Lattice.State :=
  (mkUnit01 E hE0 hE1, mkUnit01 T hT0 hT1)

/-
We choose rational lattice coordinates (all in [0,1]) as a consistent mapping scaffold.
These can be revised later; the key is: the map lands inside the unit square.
-/
def sephiraState : Sephira -> Coherence.Lattice.State
  | .keter     => mkState 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  | .chokmah   => mkState ((9:Real)/10) ((7:Real)/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  | .binah     => mkState ((7:Real)/10) ((9:Real)/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  | .chesed    => mkState ((4:Real)/5) ((3:Real)/5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  | .gevurah   => mkState ((3:Real)/5) ((4:Real)/5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  | .tiphereth => mkState ((3:Real)/4) ((3:Real)/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  | .netzach   => mkState ((3:Real)/5) ((2:Real)/5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  | .hod       => mkState ((2:Real)/5) ((3:Real)/5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  | .yesod     => mkState ((1:Real)/2) ((1:Real)/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  | .malkuth   => mkState ((1:Real)/5) ((1:Real)/5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def sephiraPsi (s : Sephira) : Real :=
  Coherence.Lattice.psi (sephiraState s)

theorem sephiraPsi_bounds (s : Sephira) :
    0 <= sephiraPsi s ∧ sephiraPsi s <= 1 := by
  -- This is inherited from psi_bounds on State
  simpa [sephiraPsi] using Coherence.Lattice.psi_bounds (sephiraState s)

end  -- noncomputable section
end TreeOfLife
end Coherence