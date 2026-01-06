import Mathlib

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace MusicScaffoldEval

/-!
# MusicScaffoldEval (with summaries)

Float-only eval (non-proof) that prints:
1) Scale table CSV: name,ratio,freqHz
2) Chord table CSV: chord,expectedOk,ok,ratios,freqsHz
3) Global summary row: chord="__SUMMARY__", okAll

This is a regression-friendly artifact for Python diffing and engine validation.
-/

def ratToFloat (r : Rat) : Float :=
  (Float.ofInt r.num) / (Float.ofNat r.den)

def ratToString (r : Rat) : String := s!"{r}"

-- Canonical ratios (Rat)
def unison : Rat := (1 : Rat)
def m3 : Rat := (6 : Rat) / (5 : Rat)
def M3 : Rat := (5 : Rat) / (4 : Rat)
def P4 : Rat := (4 : Rat) / (3 : Rat)
def P5 : Rat := (3 : Rat) / (2 : Rat)
def octave : Rat := (2 : Rat)

def scale0 : List (String × Rat) :=
  [("unison", unison), ("m3", m3), ("M3", M3), ("P4", P4), ("P5", P5), ("octave", octave)]

def consonantSet : List Rat := [unison, M3, P4, P5, octave]

def isConsonant (r : Rat) : Bool := decide (r ∈ consonantSet)
def chordOK (rs : List Rat) : Bool := rs.all isConsonant

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
-- Chord CSV + summaries
-- -------------------------
structure ChordCase where
  name : String
  expectedOk : Bool
  ratios : List Rat
deriving Repr

def chordCases : List ChordCase :=
  [ { name := "fifth+octave", expectedOk := true,  ratios := [unison, P5, octave] }
  , { name := "majorTriad",   expectedOk := true,  ratios := [unison, M3, P5] }
  , { name := "minorTriad",   expectedOk := false, ratios := [unison, m3, P5] }  -- m3 not in consonantSet stub
  , { name := "mixed",        expectedOk := false, ratios := [unison, m3, P4] }  -- m3 not in consonantSet stub
  ]

def csvHeaderChord : String := "chord,expectedOk,ok,ratios,freqsHz"

def chordLine (c : ChordCase) : String :=
  let ok := chordOK c.ratios
  let rsS := joinComma (c.ratios.map ratToString)
  let fsS := joinComma (c.ratios.map (fun r => s!"{freqOf r}"))
  s!"{c.name},{c.expectedOk},{ok},{rsS},{fsS}"

def okCase (c : ChordCase) : Bool :=
  (chordOK c.ratios) == c.expectedOk

def okAll : Bool :=
  chordCases.all okCase

def summaryLine : String :=
  s!"__SUMMARY__,,{okAll},,"

def emit : IO Unit := do
  -- Scale table
  IO.println "# SCALE"
  IO.println csvHeaderScale
  for p in scale0 do
    IO.println (csvLineScale p)

  IO.println ""
  -- Chord table
  IO.println "# CHORDS"
  IO.println csvHeaderChord
  for c in chordCases do
    IO.println (chordLine c)

  -- Global summary row
  IO.println "# SUMMARY"
  IO.println csvHeaderChord
  IO.println summaryLine

#eval emit

end MusicScaffoldEval
end Coherence