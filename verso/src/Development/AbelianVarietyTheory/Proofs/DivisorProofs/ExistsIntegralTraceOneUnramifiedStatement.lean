import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralTraceOneUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIntegralTraceOneUnramified.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_integral_trace_one_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∃ t : E, IsIntegral ℤ t ∧ t + cc t = 1 := by
  first | exact @GlobalTheory.LieDisc.exists_integral_add_cc_eq_one | exact GlobalTheory.LieDisc.exists_integral_add_cc_eq_one | (intros; apply GlobalTheory.LieDisc.exists_integral_add_cc_eq_one <;> assumption)
