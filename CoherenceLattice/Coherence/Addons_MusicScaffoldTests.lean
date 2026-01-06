import Mathlib
import CoherenceLattice.Coherence.MusicScaleScaffoldAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Coherence

noncomputable section

open Coherence.MusicScaffold

-- Scale has 6 entries
example : scaleRat0_named.length = 6 := by
  simp [scaleRat0_named]

-- Major profile accepts [unison, P5, octave]
example : chordOKRat_major [unisonRat, P5Rat, octaveRat] = true := by
  simp [chordOKRat_major, chordOKRat, consonantSetRat_major, unisonRat, P5Rat, octaveRat]

-- Minor-friendly profile accepts [unison, m3, P5]
example : chordOKRat_minor [unisonRat, m3Rat, P5Rat] = true := by
  simp [chordOKRat_minor, chordOKRat, consonantSetRat_minor, unisonRat, m3Rat, P5Rat]

end
end Coherence