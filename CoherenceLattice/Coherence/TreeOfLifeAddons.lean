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
# TreeOfLifeAddons (synced mapping)

We keep E/T assignments in ONE place as unit fractions (Nat/Nat), then derive:

- Real state (for proofs + lattice mapping)
- Float eval (via UnitFrac.toFloat in the eval file)

To tweak E/T:
- edit EFrac / TFrac tables below (num/den)

This is a mapping layer, not a claim of physics.
-/

inductive Sephira
  | keter | chokmah | binah | chesed | gevurah | tiphereth | netzach | hod | yesod | malkuth
deriving DecidableEq, Repr

/-- A fraction num/den in [0,1], with proofs. -/
structure UnitFrac where
  num : Nat
  den : Nat
  hden : 0 < den
  hle  : num <= den

def UnitFrac.toReal (u : UnitFrac) : Real :=
  (u.num : Real) / (u.den : Real)

def UnitFrac.toFloat (u : UnitFrac) : Float :=
  (Float.ofNat u.num) / (Float.ofNat u.den)

lemma UnitFrac.toReal_nonneg (u : UnitFrac) : 0 <= u.toReal := by
  have hnum : 0 <= (u.num : Real) := by
    exact_mod_cast (Nat.zero_le u.num)
  have hdenpos : 0 < (u.den : Real) := by
    exact_mod_cast u.hden
  exact div_nonneg hnum (le_of_lt hdenpos)

lemma UnitFrac.toReal_le_one (u : UnitFrac) : u.toReal <= 1 := by
  have hdenpos : 0 < (u.den : Real) := by
    exact_mod_cast u.hden
  have hleR : (u.num : Real) <= (u.den : Real) := by
    exact_mod_cast u.hle
  have hdiv :
      (u.num : Real) / (u.den : Real) <= (u.den : Real) / (u.den : Real) := by
    exact div_le_div_of_nonneg_right hleR (le_of_lt hdenpos)
  have hdenne : (u.den : Real) ≠ 0 := by
    exact ne_of_gt hdenpos
  simpa [UnitFrac.toReal, hdenne] using hdiv

def UnitFrac.toUnit01 (u : UnitFrac) : Coherence.Lattice.Unit01 :=
  ⟨u.toReal, ⟨u.toReal_nonneg, u.toReal_le_one⟩⟩

/-- Helper for literals (keeps tables clean). -/
def uf (n d : Nat) (hden : 0 < d) (hle : n <= d) : UnitFrac :=
  { num := n, den := d, hden := hden, hle := hle }

-- ======================================================
-- SINGLE SOURCE OF TRUTH: E/T assignment tables
-- Edit these to tweak the mapping.
-- ======================================================

def EFrac : Sephira -> UnitFrac
  | .keter     => uf 1 1 (by decide) (by decide)
  | .chokmah   => uf 9 10 (by decide) (by decide)
  | .binah     => uf 7 10 (by decide) (by decide)
  | .chesed    => uf 4 5 (by decide) (by decide)
  | .gevurah   => uf 3 5 (by decide) (by decide)
  | .tiphereth => uf 3 4 (by decide) (by decide)
  | .netzach   => uf 3 5 (by decide) (by decide)
  | .hod       => uf 2 5 (by decide) (by decide)
  | .yesod     => uf 1 2 (by decide) (by decide)
  | .malkuth   => uf 1 5 (by decide) (by decide)

def TFrac : Sephira -> UnitFrac
  | .keter     => uf 1 1 (by decide) (by decide)
  | .chokmah   => uf 7 10 (by decide) (by decide)
  | .binah     => uf 9 10 (by decide) (by decide)
  | .chesed    => uf 3 5 (by decide) (by decide)
  | .gevurah   => uf 4 5 (by decide) (by decide)
  | .tiphereth => uf 3 4 (by decide) (by decide)
  | .netzach   => uf 2 5 (by decide) (by decide)
  | .hod       => uf 3 5 (by decide) (by decide)
  | .yesod     => uf 1 2 (by decide) (by decide)
  | .malkuth   => uf 1 5 (by decide) (by decide)

/-- Sephira mapped into the coherence lattice State (E,T) in [0,1]^2. -/
def sephiraState (s : Sephira) : Coherence.Lattice.State :=
  ((EFrac s).toUnit01, (TFrac s).toUnit01)

def sephiraPsi (s : Sephira) : Real :=
  Coherence.Lattice.psi (sephiraState s)

theorem sephiraPsi_bounds (s : Sephira) :
    0 <= sephiraPsi s ∧ sephiraPsi s <= 1 := by
  simpa [sephiraPsi] using Coherence.Lattice.psi_bounds (sephiraState s)

end
end TreeOfLife
end Coherence