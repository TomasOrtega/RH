import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StereographicMeasureChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne
open MeasureTheory
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FibLine.lintegral_comp_fsDens` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStereographicMeasureChange.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.stereographic_measure_change : ∀ g : ℝ → ℝ≥0∞, Measurable g →
    ∫⁻ x : ℂ, g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) =
      ∫⁻ t in Set.Ioo (0:ℝ) 1, g t := by
  first | exact @GlobalTheory.FibLine.lintegral_comp_fsDens | exact GlobalTheory.FibLine.lintegral_comp_fsDens | (intros; apply GlobalTheory.FibLine.lintegral_comp_fsDens <;> assumption)
