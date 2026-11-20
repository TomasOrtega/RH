import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallBoundTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.coefficient_bound_tuple : GlobalTheory.BigOn.Exp.TupLe.CoefSt := by
  first | exact @GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt | exact GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt | (intros; apply GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt <;> assumption)
