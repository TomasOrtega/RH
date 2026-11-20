import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevNegFinSumBlockDiagonalMatrix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodMetric.ChernSpan.charpolyRev_neg_blockSum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCharpolyRevNegFinSumBlockDiagonalMatrix.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.charpolyRev_neg_finSumBlockDiagonalMatrix : ∀ {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R), Matrix.charpolyRev (-(blockSum a b)) = Matrix.charpolyRev (-a) * Matrix.charpolyRev (-b) := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.charpolyRev_neg_blockSum | exact GlobalTheory.GoodMetric.ChernSpan.charpolyRev_neg_blockSum | (intros; apply GlobalTheory.GoodMetric.ChernSpan.charpolyRev_neg_blockSum <;> assumption)
