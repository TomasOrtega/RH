import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockTwoLtTop
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IntBall.lintegral_hB_one_two_lt_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLintegralCutoffGramBoundMixedBlockTwoLtTop.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_two_lt_top : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  first | exact @GlobalTheory.IntBall.lintegral_hB_one_two_lt_top | exact GlobalTheory.IntBall.lintegral_hB_one_two_lt_top | (intros; apply GlobalTheory.IntBall.lintegral_hB_one_two_lt_top <;> assumption)
