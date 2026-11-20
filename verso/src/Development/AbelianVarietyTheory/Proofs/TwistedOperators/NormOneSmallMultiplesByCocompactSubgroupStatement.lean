import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneSmallMultiplesByCocompactSubgroup
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.normOne_small_multiples_by_cocompact_subgroup : GlobalTheory.RegSS.NormOnePacking := by
  first | exact @GlobalTheory.RegSS.normOnePacking | exact GlobalTheory.RegSS.normOnePacking | (intros; apply GlobalTheory.RegSS.normOnePacking <;> assumption)
