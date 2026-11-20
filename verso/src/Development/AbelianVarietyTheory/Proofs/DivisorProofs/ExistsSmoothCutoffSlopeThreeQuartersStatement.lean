import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothCutoffSlopeThreeQuarters
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_isCut₂` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSmoothCutoffSlopeThreeQuarters.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.exists_smoothCutoff_slope_three_quarters : ∀ T : ℝ, ∃ θ : ℝ → ℝ, IsCut T θ := by
  first | exact @GlobalTheory.exists_isCut₂ | exact GlobalTheory.exists_isCut₂ | (intros; apply GlobalTheory.exists_isCut₂ <;> assumption)
