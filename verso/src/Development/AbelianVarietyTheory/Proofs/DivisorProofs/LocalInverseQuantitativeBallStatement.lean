import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalInverseQuantitativeBall
import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.contDiffOn_one_injOn_ball_det_norm_bounds` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalInverseQuantitativeBall.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.local_inverse_quantitative_ball : ∀ {d : ℕ} (U : Set (ReciprocityTheory.L2DbarEstimates.V d)) (v₀ : ReciprocityTheory.L2DbarEstimates.V d) (Ψ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d), IsOpen U → v₀ ∈ U → ContDiffOn ℝ 1 Ψ U → Function.Bijective (fderiv ℝ Ψ v₀) → ∃ r J L : ℝ, 0 < r ∧ 0 < J ∧ 0 ≤ L ∧ Metric.ball v₀ r ⊆ U ∧ Set.InjOn Ψ (Metric.ball v₀ r) ∧ ∀ v ∈ Metric.ball v₀ r, J ≤ |(fderiv ℝ Ψ v).det| ∧ ‖fderiv ℝ Ψ v‖ ≤ L := by
  first | exact @GlobalTheory.contDiffOn_one_injOn_ball_det_norm_bounds | exact GlobalTheory.contDiffOn_one_injOn_ball_det_norm_bounds | (intros; apply GlobalTheory.contDiffOn_one_injOn_ball_det_norm_bounds <;> assumption)
