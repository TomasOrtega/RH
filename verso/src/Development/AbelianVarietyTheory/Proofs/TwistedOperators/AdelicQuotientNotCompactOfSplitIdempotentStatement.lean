import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientNotCompactOfSplitIdempotent
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.adelic_quotient_not_compact_of_split_idempotent : GlobalTheory.RegSS.IdempotentDet → GlobalTheory.RegSS.NotCompactOfIdempotent := by
  first | exact @GlobalTheory.RegSS.notCompactOfIdempotent_of | exact GlobalTheory.RegSS.notCompactOfIdempotent_of | (intros; apply GlobalTheory.RegSS.notCompactOfIdempotent_of <;> assumption)
