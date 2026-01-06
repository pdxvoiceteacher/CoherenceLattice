import Mathlib
import CoherenceLattice.Coherence.TreeOfLifeAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace TreeOfLifeBandCSV

open Coherence.TreeOfLife

structure BandThresholds where
  t0 : Float
  t1 : Float
  t2 : Float
  t3 : Float
deriving Repr

-- tweak thresholds here (default 0.2/0.4/0.6/0.8)
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

def all : List Sephira :=
  [.keter, .chokmah, .binah, .chesed, .gevurah, .tiphereth, .netzach, .hod, .yesod, .malkuth]

def EFloat (s : Sephira) : Float := (EFrac s).toFloat
def TFloat (s : Sephira) : Float := (TFrac s).toFloat
def psiFloat (s : Sephira) : Float := (EFloat s) * (TFloat s)

def csvHeader : String := "name,E,T,psi,band"
def csvLine (thr : BandThresholds) (s : Sephira) : String :=
  let e := EFloat s
  let t := TFloat s
  let p := psiFloat s
  let b := bandF thr p
  s!"{sephiraName s},{e},{t},{p},{b}"

def emitCSV : IO Unit := do
  IO.println csvHeader
  for s in all do
    IO.println (csvLine thr0 s)

#eval emitCSV

end TreeOfLifeBandCSV
end Coherence