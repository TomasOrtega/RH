import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegrableOnMinorFin
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FIntegrableOnMinorFin.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.integrableOn_inv_norm_det_pow_near_indefinite_gram : ∀ (p q n : ℕ), 2 * (p + q) ≤ n → ∃ δ₀ : ℝ, 0 < δ₀ ∧ IntegrableOn (fun y : (Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ => (‖(Matrix.of y).toBlocks₁₁.det‖ ^ n)⁻¹) {y | ∀ a b, ‖((Matrix.of y)ᵀ * Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ) * (Matrix.of y).map conj - Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ)) a b‖ < δ₀} volume := by
  first | exact @GlobalTheory.MinorInt.integrableOn_minor_fin | exact GlobalTheory.MinorInt.integrableOn_minor_fin | (intros; apply GlobalTheory.MinorInt.integrableOn_minor_fin <;> assumption)
