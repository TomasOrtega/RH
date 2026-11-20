import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodsInvariantFunctional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodsOnLineOfInvLine
open GlobalTheory.RowClaim GlobalTheory.RowReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RowReal.invLine_big` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRowTestDefinitePeriodsInvariantFunctional.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.rowTest_definitePeriods_invariant_functional : Big fun ch => InvLine ch := by
  first | exact @GlobalTheory.RowReal.invLine_big | exact GlobalTheory.RowReal.invLine_big | (intros; apply GlobalTheory.RowReal.invLine_big <;> assumption)
