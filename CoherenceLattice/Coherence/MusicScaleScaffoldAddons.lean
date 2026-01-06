import Mathlib
import CoherenceLattice.Coherence.MusicRatioAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace MusicScaffold

/-!
# MusicScaleScaffoldAddons (profiles)

Single source of truth for consonance profiles:

- Rat profiles (computable, used by eval tooling)
- Real profiles (proof-facing, derived from Rat ratios)

Profiles:
- Major-ish consonance: [unison, M3, P4, P5, octave]
- Minor-friendly:       [unison, m3, P4, P5, octave]
-/

-- =========================
-- Rat layer (computable)
-- =========================
abbrev RatioRat : Type := Rat
abbrev ScaleRat : Type := List RatioRat

def unisonRat : RatioRat := (1 : Rat)
def m3Rat : RatioRat := (6 : Rat) / (5 : Rat)
def M3Rat : RatioRat := (5 : Rat) / (4 : Rat)
def P4Rat : RatioRat := (4 : Rat) / (3 : Rat)
def P5Rat : RatioRat := (3 : Rat) / (2 : Rat)
def octaveRat : RatioRat := (2 : Rat)

def scaleRat0_named : List (String × RatioRat) :=
  [("unison", unisonRat), ("m3", m3Rat), ("M3", M3Rat), ("P4", P4Rat), ("P5", P5Rat), ("octave", octaveRat)]

-- Consonance profiles (Rat)
def consonantSetRat_major : List RatioRat := [unisonRat, M3Rat, P4Rat, P5Rat, octaveRat]
def consonantSetRat_minor : List RatioRat := [unisonRat, m3Rat, P4Rat, P5Rat, octaveRat]

def chordOKRat (profile : List RatioRat) (rs : List RatioRat) : Bool :=
  rs.all (fun r => decide (r ∈ profile))

def chordOKRat_major (rs : List RatioRat) : Bool := chordOKRat consonantSetRat_major rs
def chordOKRat_minor (rs : List RatioRat) : Bool := chordOKRat consonantSetRat_minor rs

-- =========================
-- Real layer (proof-facing)
-- =========================
noncomputable section

abbrev Ratio : Type := Real
abbrev Scale : Type := List Ratio

def ratToReal (r : RatioRat) : Real := (r : Real)

def unison : Ratio := ratToReal unisonRat
def m3 : Ratio := ratToReal m3Rat
def M3 : Ratio := ratToReal M3Rat
def P4 : Ratio := ratToReal P4Rat
def P5 : Ratio := ratToReal P5Rat
def octave : Ratio := ratToReal octaveRat

def applyRatio (f : Real) (r : Ratio) : Real := f * r
def applyScale (f : Real) (s : Scale) : List Real := s.map (fun r => applyRatio f r)

-- Real profiles (kept explicit for simp-friendly proofs)
def consonantSet_major : Scale := [unison, M3, P4, P5, octave]
def consonantSet_minor : Scale := [unison, m3, P4, P5, octave]

def isConsonantIn (profile : Scale) (r : Ratio) : Prop := r ∈ profile
def chordOK (profile : Scale) (rs : List Ratio) : Prop := List.Forall (isConsonantIn profile) rs

def chordOK_major (rs : List Ratio) : Prop := chordOK consonantSet_major rs
def chordOK_minor (rs : List Ratio) : Prop := chordOK consonantSet_minor rs

lemma unison_consonant_major : isConsonantIn consonantSet_major unison := by
  simp [isConsonantIn, consonantSet_major]

end
end MusicScaffold
end Coherence