import Mathlib

/- English proof (translation)
Introduce `K _ n U T hU hT i j hij`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge k i with hk | hk` into its components or cases. Rewrite using `[hU i k hk, zero_mul]`.

Rewrite using `[hT k j (lt_of_lt_of_le hij hk), mul_zero]`.
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
