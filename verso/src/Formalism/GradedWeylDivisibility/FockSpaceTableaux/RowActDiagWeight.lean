import Formalism.GradedWeylDivisibility.StatementD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `R _ k n t μ f hf`. Establish `hX : (rowAct R (n` using `n) (Matrix.diagonal t)) = aeval fun v : Fin k × Fin n => C (t v.1) * X v := by`. Unfold `rowAct`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Simplify using `only [Matrix.diagonal_apply]`. Rewrite using `[Finset.sum_eq_single v.1]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`.

Simplify using the standard rewrite rules. Establish `hwt : ∀ (d : Fin k × Fin n →₀ ℕ) (a : Fin k), Finsupp.weight (rowW k n) d a = ∑ s, d (a, s)`. Introduce `d a`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]`. Simplify using `only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`.

Rewrite using `[Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb, Ne.symm hb]`. Simplify using the standard rewrite rules.

Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hw : Finsupp.weight (rowW k n) d = μ` using `hf (mem_support_iff.mp hd)`.

Establish `hp : (d.prod fun v e => t v.1 ^ e) = ∏ a, t a ^ μ a`. Rewrite using `[← hw, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hwt]`. Simplify using `only`.

Rewrite using `[Finset.prod_pow_eq_pow_sum]`. Rewrite using `[hX, aeval_monomial, ← hp, smul_eq_C_mul, monomial_eq]`. Simplify using `only [mul_pow, Finsupp.prod_mul, map_finsuppProd, map_pow, MvPolynomial.algebraMap_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem row_action_diagonal_weight : RowActDiagWeight := by
  intro R _ k n t μ f hf
  have hX : (rowAct R (n := n) (Matrix.diagonal t)) = aeval fun v : Fin k × Fin n => C (t v.1) * X v := by
    unfold rowAct
    congr 1
    funext v
    simp only [Matrix.diagonal_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  have hwt : ∀ (d : Fin k × Fin n →₀ ℕ) (a : Fin k), Finsupp.weight (rowW k n) d a = ∑ s, d (a, s) := by
    intro d a
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
      Fintype.sum_prod_type]
    simp only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [hb, Ne.symm hb]
    · simp
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (rowW k n) d = μ := hf (mem_support_iff.mp hd)
  have hp : (d.prod fun v e => t v.1 ^ e) = ∏ a, t a ^ μ a := by
    rw [← hw, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hwt]
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hX, aeval_monomial, ← hp, smul_eq_C_mul, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, map_finsuppProd, map_pow, MvPolynomial.algebraMap_eq]
  ring

end Formalism.GradedWeylDivisibility
