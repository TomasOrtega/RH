import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFubiniStudyDensityEqOne
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.lintegral_fubiniStudy_density_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLintegralFubiniStudyDensityEqOne.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.lintegral_fubiniStudy_density_eq_one' : ∀ n : ℕ, ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n, ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) = 1 := by
  first | exact @GlobalTheory.lintegral_fubiniStudy_density_eq_one | exact GlobalTheory.lintegral_fubiniStudy_density_eq_one | (intros; apply GlobalTheory.lintegral_fubiniStudy_density_eq_one <;> assumption)
