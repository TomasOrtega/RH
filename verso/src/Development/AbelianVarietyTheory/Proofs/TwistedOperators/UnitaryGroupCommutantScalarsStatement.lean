import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupCommutantScalars
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.unitaryGroup_commutant_scalars : GlobalTheory.RegSS.UnitaryCommutant := by
  first | exact @GlobalTheory.RegSS.unitaryCommutant | exact GlobalTheory.RegSS.unitaryCommutant | (intros; apply GlobalTheory.RegSS.unitaryCommutant <;> assumption)
