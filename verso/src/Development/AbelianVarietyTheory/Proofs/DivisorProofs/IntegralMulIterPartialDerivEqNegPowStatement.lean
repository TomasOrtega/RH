import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulIterPartialDerivEqNegPow
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HCA.integral_mul_dw_eq_neg_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralMulIterPartialDerivEqNegPow.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.integral_mul_iterPartialDeriv_eq_neg_pow : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d)) (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w u x * φ x := by
  first | exact @GlobalTheory.HCA.integral_mul_dw_eq_neg_pow | exact GlobalTheory.HCA.integral_mul_dw_eq_neg_pow | (intros; apply GlobalTheory.HCA.integral_mul_dw_eq_neg_pow <;> assumption)
