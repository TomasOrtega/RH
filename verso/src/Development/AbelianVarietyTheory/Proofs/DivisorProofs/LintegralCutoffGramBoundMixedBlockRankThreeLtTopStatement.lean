import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankThreeLtTop
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLintegralCutoffGramBoundMixedBlockRankThreeLtTop.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankThree_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 2) → ∫⁻ w : Low 3 → ℂ, hB p0 w < ⊤ := by
  first | exact @GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top | exact GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top | (intros; apply GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top <;> assumption)
