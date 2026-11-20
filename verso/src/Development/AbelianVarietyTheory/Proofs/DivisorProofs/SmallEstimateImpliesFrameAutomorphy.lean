import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphyFromSmallExponentStatement

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GlobalTheory.FrameAut.autSt_of_smallSt : GlobalTheory.ExpTie.SmallSt → GlobalTheory.FrameAut.AutSt :=
  GlobalTheory.T.automorphy_from_small_exponent
