import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumsDbarCohomologous
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCurvaturePowerSumsDbarCohomologous.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.curvaturePowerSums_dbarCohomologous : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k, DbarCoh A (powFld A G k) (powFld A G' k) := by
  first | exact @GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld | exact GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld | (intros; apply GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld <;> assumption)
