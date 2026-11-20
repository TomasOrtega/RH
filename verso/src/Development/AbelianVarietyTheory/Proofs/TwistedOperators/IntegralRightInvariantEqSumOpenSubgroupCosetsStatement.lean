import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosets
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIntegralRightInvariantEqSumOpenSubgroupCosets.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets : CosetIntegral := by
  first | exact @GlobalTheory.InertZeta.cosetIntegral_holds | exact GlobalTheory.InertZeta.cosetIntegral_holds | (intros; apply GlobalTheory.InertZeta.cosetIntegral_holds <;> assumption)
