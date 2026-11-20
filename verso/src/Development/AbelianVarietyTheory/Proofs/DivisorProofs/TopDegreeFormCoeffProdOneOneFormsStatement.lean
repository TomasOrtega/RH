import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffProdOneOneForms
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodTop.topCoeff_prod_forms` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTopDegreeFormCoeffProdOneOneForms.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_prod_oneOneForms : ∀ {n : ℕ} (k : Fin n → Fin n → Fin n → ℂ), topCoeff (∏ i, ∑ a, ∑ b, MvPolynomial.C (k i a b) * MvPolynomial.X (a, b)) = ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i b => k i (u i) b).det := by
  first | exact @GlobalTheory.GoodTop.topCoeff_prod_forms | exact GlobalTheory.GoodTop.topCoeff_prod_forms | (intros; apply GlobalTheory.GoodTop.topCoeff_prod_forms <;> assumption)
