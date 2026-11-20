import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFderivChartLeOfBoundedLieDerivatives
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JSW.norm_fderiv_chart_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNormFderivChartLeOfBoundedLieDerivatives.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.norm_fderiv_chart_le_of_bounded_lieDerivatives : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) →
      ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖ := by
  first | exact @GlobalTheory.JSW.norm_fderiv_chart_le | exact GlobalTheory.JSW.norm_fderiv_chart_le | (intros; apply GlobalTheory.JSW.norm_fderiv_chart_le <;> assumption)
