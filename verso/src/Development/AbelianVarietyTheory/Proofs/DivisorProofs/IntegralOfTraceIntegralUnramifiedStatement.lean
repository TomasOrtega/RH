import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfTraceIntegralUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralOfTraceIntegralUnramified.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.integral_of_trace_integral_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : E, (∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (w * a + cc (w * a))) → IsIntegral ℤ w := by
  first | exact @GlobalTheory.LieDisc.isIntegral_of_trace_integral | exact GlobalTheory.LieDisc.isIntegral_of_trace_integral | (intros; apply GlobalTheory.LieDisc.isIntegral_of_trace_integral <;> assumption)
