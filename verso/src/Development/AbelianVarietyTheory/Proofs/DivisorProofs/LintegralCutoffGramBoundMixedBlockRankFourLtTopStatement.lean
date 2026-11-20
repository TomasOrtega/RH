import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankFourLtTop
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLintegralCutoffGramBoundMixedBlockRankFourLtTop.lean&line=134#L134)
-/
theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankFour_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 3) → ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  first | exact @GlobalTheory.IntBall.Fin4.lintegral_hB_four_lt_top | exact GlobalTheory.IntBall.Fin4.lintegral_hB_four_lt_top | (intros; apply GlobalTheory.IntBall.Fin4.lintegral_hB_four_lt_top <;> assumption)
