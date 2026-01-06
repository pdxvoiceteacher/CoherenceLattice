import Mathlib
import CoherenceLattice.Coherence.TreeOfLifeAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace TreeOfLifeBandEval

/-!
# TreeOfLifeBandEval (synced)

Float-only sanity output (NOT a theorem).

This file derives E/T from TreeOfLifeAddons.EFrac/TFrac, so it stays synced.
To tweak thresholds, edit `thr0` below.
-/

open Coherence.TreeOfLife

structure BandThresholds where
  t0 : Float
  t1 : Float
  t2 : Float
  t3 : Float
deriving Repr

-- TWEAK THRESHOLDS HERE (default: 0.2/0.4/0.6/0.8)
def thr0 : BandThresholds := { t0 := 0.2, t1 := 0.4, t2 := 0.6, t3 := 0.8 }

def bandF (thr : BandThresholds) (psi : Float) : Nat :=
  if psi < thr.t0 then 0
  else if psi < thr.t1 then 1
  else if psi < thr.t2 then 2
  else if psi < thr.t3 then 3
  else 4

def sephiraName : Sephira -> String
  | .keter     => "keter"
  | .chokmah   => "chokmah"
  | .binah     => "binah"
  | .chesed    => "chesed"
  | .gevurah   => "gevurah"
  | .tiphereth => "tiphereth"
  | .netzach   => "netzach"
  | .hod       => "hod"
  | .yesod     => "yesod"
  | .malkuth   => "malkuth"

def EFloat (s : Sephira) : Float := (EFrac s).toFloat
def TFloat (s : Sephira) : Float := (TFrac s).toFloat

structure Row where
  name : String
  E : Float
  T : Float
  psi : Float
  band : Nat
deriving Repr

def row (thr : BandThresholds) (s : Sephira) : Row :=
  let e := EFloat s
  let t := TFloat s
  let p := e * t
  { name := sephiraName s, E := e, T := t, psi := p, band := bandF thr p }

def all : List Sephira :=
  [.keter, .chokmah, .binah, .chesed, .gevurah, .tiphereth, .netzach, .hod, .yesod, .malkuth]

def rows : List Row := all.map (row thr0)

def csvHeader : String := "name,E,T,psi,band"
def csvLine (r : Row) : String :=
  s!"{r.name},{r.E},{r.T},{r.psi},{r.band}"

def csv : String := String.intercalate "\n" (csvHeader :: rows.map csvLine)

#eval thr0
#eval rows
#eval csv

end TreeOfLifeBandEval
end Coherence