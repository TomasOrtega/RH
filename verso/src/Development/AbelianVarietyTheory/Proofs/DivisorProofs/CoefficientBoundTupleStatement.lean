import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.trace_bound_tuple : GlobalTheory.BigOn.Exp.TupLe.TraceSt := by
  first | exact @GlobalTheory.BigOn.Exp.TupLe.traceSt | exact GlobalTheory.BigOn.Exp.TupLe.traceSt | (intros; apply GlobalTheory.BigOn.Exp.TupLe.traceSt <;> assumption)
