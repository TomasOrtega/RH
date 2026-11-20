import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FCyclicVectorOfSeparableCharpolyField.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.cyclicVector_of_separable_charpoly_field : GlobalTheory.RegSS.CyclicField := by
  first | exact @GlobalTheory.RegSS.cyclicField | exact GlobalTheory.RegSS.cyclicField | (intros; apply GlobalTheory.RegSS.cyclicField <;> assumption)
