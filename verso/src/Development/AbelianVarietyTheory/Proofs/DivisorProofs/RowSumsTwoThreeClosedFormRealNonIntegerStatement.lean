import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumsTwoThreeClosedFormRealNonInteger
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WpFam.RowReal.row_real` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRowSumsTwoThreeClosedFormRealNonInteger.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger : ∀ w : ℂ, w.im = 0 → (∀ n : ℤ, w ≠ n) → (∑' m : ℤ, 1 / (w + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 2)) ∧ ∑' m : ℤ, 1 / (w + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 3) := by
  first | exact @GlobalTheory.WpFam.RowReal.row_real | exact GlobalTheory.WpFam.RowReal.row_real | (intros; apply GlobalTheory.WpFam.RowReal.row_real <;> assumption)
