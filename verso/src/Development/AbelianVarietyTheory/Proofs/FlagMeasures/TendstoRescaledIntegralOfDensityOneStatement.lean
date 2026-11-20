import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoRescaledIntegralOfDensityOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvSubOneMem
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FTendstoRescaledIntegralOfDensityOne.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.tendsto_rescaled_integral_of_ball_density_bounds : ∀ (d : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ν → (∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ → ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), ν (Metric.closedBall x r) ≤ ENNReal.ofReal κ * volume (Metric.closedBall x r) ∧ volume (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r)) → ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, Continuous φ → HasCompactSupport φ → Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x, φ x)) := by
  first | exact @GlobalTheory.tendsto_rescaled_integral_of_density_one | exact GlobalTheory.tendsto_rescaled_integral_of_density_one | (intros; apply GlobalTheory.tendsto_rescaled_integral_of_density_one <;> assumption)
