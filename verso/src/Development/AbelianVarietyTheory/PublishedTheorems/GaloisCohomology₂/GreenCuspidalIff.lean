import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

open Polynomial

namespace GlobalTheory.Published

def GreenCuspidal : Prop := GlobalTheory.GLq.Green

/- English proof (translation)
The claim follows from `h`.
-/
theorem GreenCuspidal.green (h : GreenCuspidal) : GlobalTheory.GLq.Green := h

end GlobalTheory.Published
