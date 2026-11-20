import Mathlib

open MvPolynomial

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities.
-/
theorem RootFieldNumerics.map_prod_linear (J : Type) [Fintype J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ)
    (c : Fin d → J → ℝ) :
    Φ (∏ k, ∑ j, C (c k j) * X j) =
      ∑ w : Fin d → J, (∏ k, c k (w k)) * Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  classical
  rw [Fintype.prod_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hX : ∏ k, (C (c k (w k)) * X (w k) : MvPolynomial J ℝ) =
      (∏ k, c k (w k)) • monomial (∑ k, Finsupp.single (w k) 1) (1 : ℝ) := by
    rw [Finset.prod_mul_distrib, monomial_sum_one, ← C_mul', map_prod]
    rfl
  rw [hX, map_smul, smul_eq_mul]
