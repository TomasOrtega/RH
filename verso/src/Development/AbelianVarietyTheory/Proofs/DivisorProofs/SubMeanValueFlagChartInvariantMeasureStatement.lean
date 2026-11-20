import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMeanValueFlagChartInvariantMeasure
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SubmeanChart.submean_chart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSubMeanValueFlagChartInvariantMeasure.lean&line=94#L94)
-/
theorem _root_.GlobalTheory.T.subMeanValue_flagChart_invariantMeasure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r) (P : Frame X.Ψ r → ℂ), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w → DifferentiableOn ℂ P X.dom → ENNReal.ofReal (X.pnorm la P x ^ 2) ≤ ENNReal.ofReal (2 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r) * ∫⁻ z in Metric.ball (0 : V (nd X)) (chartRad E r w), ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
  first | exact @GlobalTheory.SubmeanChart.submean_chart | exact GlobalTheory.SubmeanChart.submean_chart | (intros; apply GlobalTheory.SubmeanChart.submean_chart <;> assumption)
