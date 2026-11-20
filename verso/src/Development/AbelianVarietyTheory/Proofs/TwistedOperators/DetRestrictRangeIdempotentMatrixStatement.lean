import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetRestrictRangeIdempotentMatrix
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.RegSS.idempotentDet | exact GlobalTheory.RegSS.idempotentDet | (intros; apply GlobalTheory.RegSS.idempotentDet <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.det_restrict_range_idempotent_matrix : GlobalTheory.RegSS.IdempotentDet := by
  first | exact @GlobalTheory.RegSS.idempotentDet | exact GlobalTheory.RegSS.idempotentDet | (intros; apply GlobalTheory.RegSS.idempotentDet <;> assumption)
