import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantDiagonalBlockUnitLowerPos
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FColumnGramDeterminantDiagonalBlockUnitLowerPos.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.columnGramDeterminant_diagonalBlockUnitLower_pos : ∀ (r p0 : ℕ) (w : Low r → ℂ) (k : Fin (r - 1 + 1)), 0 < colGram (blkW p0 w) k := by
  first | exact @GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos | exact GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos | (intros; apply GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos <;> assumption)
