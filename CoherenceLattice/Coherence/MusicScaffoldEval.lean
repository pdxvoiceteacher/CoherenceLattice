import Mathlib

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace MusicScaffoldEval

/-!
# MusicScaffoldEval

Float-only eval (non-proof) that prints:
- applyScale for a base frequency
- chord OK flags
- CSV output for Python diffing

We use Rat for exact ratios and convert Rat -> Float for frequency outputs.
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

def baseF : Float := 440.0

def freqOf (r : Rat) : Float := baseF * ratToFloat r

def csvHeaderScale : String := "name,ratio,freqHz"
def csvLineScale (p : String × Rat) : String :=
  s!"{p.1},{ratToString p.2},{freqOf p.2}"

def csvHeaderChord : String := "chord,ok,ratios,freqsHz"
def joinComma (xs : List String) : String := String.intercalate "," xs

def chordLine (name : String) (rs : List Rat) : String :=
  let ok := chordOK rs
  let rsS := joinComma (rs.map ratToString)
  let fsS := joinComma (rs.map (fun r => s!"{freqOf r}"))
  s!"{name},{ok},{rsS},{fsS}"

def emit : IO Unit := do
  -- Scale table
  IO.println csvHeaderScale
  for p in scale0 do
    IO.println (csvLineScale p)

  IO.println ""
  -- Chord flags
  IO.println csvHeaderChord
  IO.println (chordLine "fifth+octave" [unison, P5, octave])
  IO.println (chordLine "majorTriad" [unison, M3, P5])
  IO.println (chordLine "minorTriad" [unison, m3, P5])
  IO.println (chordLine "mixed" [unison, m3, P4])

#eval emit

end MusicScaffoldEval
end Coherence