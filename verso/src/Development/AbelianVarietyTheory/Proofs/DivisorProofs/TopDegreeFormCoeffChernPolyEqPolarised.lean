import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulCoeffCharpolyRevNegEqSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffProdOneOneFormsStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem topCoeff_finsum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, topCoeff (f i) := by
  simp only [topCoeff, MvPolynomial.coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem topCoeff_const_mul {n : ℕ} (a : ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (MvPolynomial.C a * P) = a * topCoeff P := by
  simp only [topCoeff, MvPolynomial.coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem topCoeff_chernPoly_eq_mixTop : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n),
    topCoeff (chernPoly G v n) = mixTop fun _ => curvAt G v := by
  intro n r _ _ G v
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have key := GlobalTheory.T.factorial_mul_coeff_charpolyRev_neg_eq_sum (curvPoly G v) n
  have h1 : (n.factorial : ℂ) * topCoeff (chernPoly G v n) =
      ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
          (Matrix.of fun i b => curvAt G v (u i) b (p i) (p (π i))).det := by
    rw [← topCoeff_const_mul, map_natCast, chernPoly, key, topCoeff_finsum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [topCoeff_finsum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ), topCoeff_const_mul]
    have hp : (∏ i, curvPoly G v (p i) (p (π i))) = ∏ i, ∑ a, ∑ b,
        MvPolynomial.C (curv G v (coordVec a) (coordVec b) (p i) (p (π i))) * MvPolynomial.X (a, b) := by
      simp [curvPoly]
    rw [hp, GlobalTheory.T.topDegreeFormCoeff_prod_oneOneForms, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [curvAt, mul_assoc]
  rw [mixTop, ← h1, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end GlobalTheory.GoodTop
