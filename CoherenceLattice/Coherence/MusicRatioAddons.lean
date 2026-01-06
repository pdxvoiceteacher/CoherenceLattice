import Mathlib

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence
namespace MusicRatio

noncomputable section

/-!
# MusicRatioAddons

Just-intonation ratios as Real. Since Real division is noncomputable in Lean,
we work in a `noncomputable section`.

Lightweight ordering lemmas use `norm_num`.
-/

def ratioUnison : Real := 1
def ratioMinorSecond : Real := (16:Real) / 15
def ratioMajorSecond : Real := (9:Real) / 8
def ratioMinorThird : Real := (6:Real) / 5
def ratioMajorThird : Real := (5:Real) / 4
def ratioFourth : Real := (4:Real) / 3
def ratioFifth : Real := (3:Real) / 2
def ratioOctave : Real := 2

def applyRatio (f r : Real) : Real := f * r

lemma ratioMinorThird_lt_majorThird : ratioMinorThird < ratioMajorThird := by
  norm_num [ratioMinorThird, ratioMajorThird]

lemma ratioMajorThird_lt_fourth : ratioMajorThird < ratioFourth := by
  norm_num [ratioMajorThird, ratioFourth]

lemma ratioFourth_lt_fifth : ratioFourth < ratioFifth := by
  norm_num [ratioFourth, ratioFifth]

lemma ratioFifth_lt_octave : ratioFifth < ratioOctave := by
  norm_num [ratioFifth, ratioOctave]

theorem consonance_chain :
    And (ratioUnison < ratioMinorThird)
      (And (ratioMinorThird < ratioMajorThird)
        (And (ratioMajorThird < ratioFourth)
          (And (ratioFourth < ratioFifth)
               (ratioFifth < ratioOctave)))) := by
  refine And.intro ?_ (And.intro ratioMinorThird_lt_majorThird (And.intro ratioMajorThird_lt_fourth (And.intro ratioFourth_lt_fifth ratioFifth_lt_octave)))
  norm_num [ratioUnison, ratioMinorThird]

end
end MusicRatio
end Coherence