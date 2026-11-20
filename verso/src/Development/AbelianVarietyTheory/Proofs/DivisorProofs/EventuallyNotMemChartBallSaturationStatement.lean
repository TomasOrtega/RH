import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyNotMemChartBallSaturation
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEventuallyNotMemChartBallSaturation.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.eventually_not_mem_chartBall_saturation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ρ : ℝ), (∀ z : V (nd X), ‖z‖ ≤ ρ → z ∈ OmF X x) → ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b) := by
  first | exact @GlobalTheory.SaturationClosed.eventually_not_mem_saturation | exact GlobalTheory.SaturationClosed.eventually_not_mem_saturation | (intros; apply GlobalTheory.SaturationClosed.eventually_not_mem_saturation <;> assumption)
