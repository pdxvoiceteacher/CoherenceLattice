import Mathlib
import CoherenceLattice.Coherence.MusicScaleScaffoldAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace MusicScaffoldEval

/-!
# MusicScaffoldEval (profiles + summaries)

Float-only eval (non-proof) that prints:

1) SCALE table CSV (from scaffold Rat ratios): name,ratio,freqHz
2) CHORDS table CSV for MAJOR profile
3) CHORDS table CSV for MINOR profile
Each with:
- expectedOk, ok, match
- global __SUMMARY__ row

Profiles are sourced from MusicScaleScaffoldAddons so eval stays synced.
-/

open Coherence.MusicScaffold

def ratToFloat (r : Rat) : Float :=
  (Float.ofInt r.num) / (Float.ofNat r.den)

def ratToString (r : Rat) : String := s!"{r}"
def joinComma (xs : List String) : String := String.intercalate "," xs

def baseF : Float := 440.0
def freqOf (r : Rat) : Float := baseF * ratToFloat r

-- -------------------------
-- Scale CSV
-- -------------------------
def csvHeaderScale : String := "name,ratio,freqHz"
def csvLineScale (p : String × Rat) : String :=
  s!"{p.1},{ratToString p.2},{freqOf p.2}"

-- -------------------------
-- Chord CSV (parameterized)
-- -------------------------
structure ChordCase where
  name : String
  expectedMajor : Bool
  expectedMinor : Bool
  ratios : List Rat
deriving Repr

def chordCases : List ChordCase :=
  [ { name := "fifth+octave", expectedMajor := true,  expectedMinor := true,  ratios := [unisonRat, P5Rat, octaveRat] }
  , { name := "majorTriad",   expectedMajor := true,  expectedMinor := false, ratios := [unisonRat, M3Rat, P5Rat] }
  , { name := "minorTriad",   expectedMajor := false, expectedMinor := true,  ratios := [unisonRat, m3Rat, P5Rat] }
  , { name := "mixed",        expectedMajor := false, expectedMinor := true,  ratios := [unisonRat, m3Rat, P4Rat] }
  ]

def csvHeaderChord : String := "profile,chord,expectedOk,ok,match,ratios,freqsHz"

def chordLine (profileName : String) (profile : List Rat) (expectedOk : Bool) (name : String) (rs : List Rat) : String :=
  let ok := chordOKRat profile rs
  let matchesOk := (ok == expectedOk)
  let rsS := joinComma (rs.map ratToString)
  let fsS := joinComma (rs.map (fun r => s!"{freqOf r}"))
  s!"{profileName},{name},{expectedOk},{ok},{matchesOk},{rsS},{fsS}"

def okAllFor (profile : List Rat) (cases : List ChordCase) (isMajor : Bool) : Bool :=
  cases.all (fun c =>
    let expected := if isMajor then c.expectedMajor else c.expectedMinor
    (chordOKRat profile c.ratios) == expected)

def emit : IO Unit := do
  -- SCALE
  IO.println "# SCALE"
  IO.println csvHeaderScale
  for p in scaleRat0_named do
    IO.println (csvLineScale p)

  IO.println ""
  -- CHORDS (MAJOR profile)
  IO.println "# CHORDS_MAJOR"
  IO.println csvHeaderChord
  for c in chordCases do
    IO.println (chordLine "major" consonantSetRat_major c.expectedMajor c.name c.ratios)
  let okMaj := okAllFor consonantSetRat_major chordCases true
  IO.println s!"major,__SUMMARY__,,{okMaj},,,"

  IO.println ""
  -- CHORDS (MINOR profile)
  IO.println "# CHORDS_MINOR"
  IO.println csvHeaderChord
  for c in chordCases do
    IO.println (chordLine "minor" consonantSetRat_minor c.expectedMinor c.name c.ratios)
  let okMin := okAllFor consonantSetRat_minor chordCases false
  IO.println s!"minor,__SUMMARY__,,{okMin},,,"

#eval emit

end MusicScaffoldEval
end Coherence