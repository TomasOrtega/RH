import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoIntegralLogAddInv
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTendstoIntegralLogAddInv.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.tendsto_integral_log_add_inv_succ : ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) [IsFiniteMeasure μ] (w : T → ℝ) (C : ℝ), Measurable w → (∀ x, 0 ≤ w x ∧ w x ≤ C) → (∀ᵐ x ∂μ, 0 < w x) → Integrable (fun x => Real.log (w x) / 2) μ → Tendsto (fun n : ℕ => ∫ x, Real.log (w x + 1 / ((n : ℝ) + 1)) ∂μ) atTop (𝓝 (2 * ∫ x, Real.log (w x) / 2 ∂μ)) := by
  first | exact @GlobalTheory.Mix.tendsto_integral_log_add_inv | exact GlobalTheory.Mix.tendsto_integral_log_add_inv | (intros; apply GlobalTheory.Mix.tendsto_integral_log_add_inv <;> assumption)
