import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphyFromSmallExponentStatement

/- English proof (translation)
The claim follows from `GlobalTheory.T.automorphy_from_small_exponent`.
-/
theorem GlobalTheory.FrameAut.autSt_of_smallSt : GlobalTheory.ExpTie.SmallSt → GlobalTheory.FrameAut.AutSt :=
  GlobalTheory.T.automorphy_from_small_exponent
