import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeProdNormSqEqAbsNormSpan
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCmTypeProdNormSqEqAbsNormSpan.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.cmType_prod_norm_sq_eq_absNorm_span : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ α : 𝓞 K, ∏ i, ‖φ i (α : K)‖ ^ 2 = ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm | exact GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm | (intros; apply GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm <;> assumption)
