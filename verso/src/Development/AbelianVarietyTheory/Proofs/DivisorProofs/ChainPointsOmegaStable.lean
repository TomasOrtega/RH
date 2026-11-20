import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainPointsReadLie

set_option autoImplicit false

namespace GlobalTheory.ChainPts

/- English proof (translation)
The claim follows from `GlobalTheory.TriFrame.readsOmSt`.
-/
theorem readsOmSt : GlobalTheory.ChainPts.ReadsOmSt := GlobalTheory.TriFrame.readsOmSt

end GlobalTheory.ChainPts
