import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HormanderEstimateOnBallConstLeviBound
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HormanderBall.hormander_ball` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHormanderEstimateOnBallConstLeviBound.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.hormander_estimate_on_ball_const_levi_bound : ∀ (n : ℕ) (c : V n) (r t : ℝ) (φ : V n → ℝ) (F0 : V n → ℂ), 0 < t → ContDiffOn ℝ ∞ φ (ball c r) → ContDiffOn ℝ ∞ F0 (ball c r) → (∀ v ∈ ball c r, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n (fun w => (φ w : ℂ)) v ξ).re) → ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball c r) ∧ ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - F v‖ ^ 2 * Real.exp (-φ v)) ≤ ENNReal.ofReal t⁻¹ * ∫⁻ v in ball c r, ENNReal.ofReal ((∑ j, ‖wdb n j F0 v‖ ^ 2) * Real.exp (-φ v)) := by
  first | exact @GlobalTheory.HormanderBall.hormander_ball | exact GlobalTheory.HormanderBall.hormander_ball | (intros; apply GlobalTheory.HormanderBall.hormander_ball <;> assumption)
