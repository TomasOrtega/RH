import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

open Polynomial

namespace GlobalTheory.Published

def GreenCuspidal : Prop := GlobalTheory.GLq.Green

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GreenCuspidal.green (h : GreenCuspidal) : GlobalTheory.GLq.Green := h

end GlobalTheory.Published
