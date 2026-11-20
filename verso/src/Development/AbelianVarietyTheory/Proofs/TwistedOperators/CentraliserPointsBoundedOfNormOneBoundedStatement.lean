import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentraliserPointsBoundedOfNormOneBounded
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.centraliser_points_bounded_of_normOne_bounded : GlobalTheory.RegSS.MatOfNormBounded := by
  first | exact @GlobalTheory.RegSS.MatBd.matOfNormBounded | exact GlobalTheory.RegSS.MatBd.matOfNormBounded | (intros; apply GlobalTheory.RegSS.MatBd.matOfNormBounded <;> assumption)
