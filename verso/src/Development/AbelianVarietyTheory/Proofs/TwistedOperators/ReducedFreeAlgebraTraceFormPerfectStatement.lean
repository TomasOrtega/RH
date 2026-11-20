import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReducedFreeAlgebraTraceFormPerfect
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.reduced_free_algebra_traceForm_perfect : GlobalTheory.RegSS.TracePerfect := by
  first | exact @GlobalTheory.RegSS.tracePerfect | exact GlobalTheory.RegSS.tracePerfect | (intros; apply GlobalTheory.RegSS.tracePerfect <;> assumption)
