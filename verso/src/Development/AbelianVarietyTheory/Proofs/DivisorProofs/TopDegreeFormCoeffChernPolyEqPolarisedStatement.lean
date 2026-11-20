import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffChernPolyEqPolarised
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTopDegreeFormCoeffChernPolyEqPolarised.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_chernPoly_eq_polarised : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), topCoeff (chernPoly G v n) = mixTop fun _ => curvAt G v := by
  first | exact @GlobalTheory.GoodTop.topCoeff_chernPoly_eq_mixTop | exact GlobalTheory.GoodTop.topCoeff_chernPoly_eq_mixTop | (intros; apply GlobalTheory.GoodTop.topCoeff_chernPoly_eq_mixTop <;> assumption)
