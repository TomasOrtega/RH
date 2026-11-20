import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorCommutant
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.RegSS.pointsCommutant | exact GlobalTheory.RegSS.pointsCommutant | (intros; apply GlobalTheory.RegSS.pointsCommutant <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.regularSemisimple_tensor_commutant : GlobalTheory.RegSS.PointsCommutant := by
  first | exact @GlobalTheory.RegSS.pointsCommutant | exact GlobalTheory.RegSS.pointsCommutant | (intros; apply GlobalTheory.RegSS.pointsCommutant <;> assumption)
