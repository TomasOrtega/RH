import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAlgCharEqArgMulAbs
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCmAlgCharEqArgMulAbs.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.cm_algChar_eq_arg_mul_abs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : (E →+* ℂ) → ℤ) (w0 : ℤ),
    (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∀ k : E, k ≠ 0 →
    (∏ w : InfinitePlace E, (w.embedding k / ((‖w.embedding k‖ : ℝ) : ℂ)) ^ (2 * n w.embedding - w0)) *
      ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ∏ φ : E →+* ℂ, φ k ^ n φ := by
  first | exact @GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs | exact GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs | (intros; apply GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs <;> assumption)
