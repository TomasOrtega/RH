import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Reformulated.B.Qe38.upper_triangular_mul :
    ∀ {K : Type} [inst : Field K] {n : ℕ}
    (U T : Matrix (Fin n) (Fin n) K),
    (∀ (i j : Fin n), j < i → U i j = (0 : K)) →
      (∀ (i j : Fin n), j < i → T i j = (0 : K)) → ∀ (i j : Fin n), j < i → (U * T) i j = (0 : K) := by
  intro K _ n U T hU hT i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with hk | hk
  · rw [hU i k hk, zero_mul]
  · rw [hT k j (lt_of_lt_of_le hij hk), mul_zero]
