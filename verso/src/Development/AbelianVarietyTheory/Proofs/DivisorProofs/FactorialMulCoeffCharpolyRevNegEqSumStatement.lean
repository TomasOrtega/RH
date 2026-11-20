import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulCoeffCharpolyRevNegEqSum
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodTop.factorial_mul_coeff_charpolyRev_neg` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFactorialMulCoeffCharpolyRevNegEqSum.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.factorial_mul_coeff_charpolyRev_neg_eq_sum : ∀ {A : Type} [CommRing A] {r : Type} [Fintype r] [DecidableEq r] (M : Matrix r r A) (n : ℕ), (n.factorial : A) * (Matrix.charpolyRev (-M)).coeff n = ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) := by
  first | exact @GlobalTheory.GoodTop.factorial_mul_coeff_charpolyRev_neg | exact GlobalTheory.GoodTop.factorial_mul_coeff_charpolyRev_neg | (intros; apply GlobalTheory.GoodTop.factorial_mul_coeff_charpolyRev_neg <;> assumption)
