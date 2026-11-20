import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerBlockLastEqOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FColumnGramDeterminantUnitLowerBlockLastEqOne.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.columnGramDeterminant_unitLowerBlock_last_eq_one : ∀ (r p0 : ℕ) (w : Low r → ℂ), colGram (blkW p0 w) (Fin.last (r - 1)) = 1 := by
  first | exact @GlobalTheory.IntBall.colGramLast | exact GlobalTheory.IntBall.colGramLast | (intros; apply GlobalTheory.IntBall.colGramLast <;> assumption)
