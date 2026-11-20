import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianTraceFormOfTraceFormPerfect
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.hermitianTraceForm_of_traceForm_perfect : GlobalTheory.RegSS.TracePerfect → GlobalTheory.RegSS.TraceClause := by
  first | exact @GlobalTheory.RegSS.traceClause_of_tracePerfect | exact GlobalTheory.RegSS.traceClause_of_tracePerfect | (intros; apply GlobalTheory.RegSS.traceClause_of_tracePerfect <;> assumption)
