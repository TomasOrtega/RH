import Mathlib

/- English proof (translation)
Introduce `R _ n A B hA hB i`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i ?_ ?_` and prove the remaining obligations. Introduce `j _ hji`. Break down `lt_or_gt_of_ne hji with h | h` into its components or cases.

Rewrite using `[hA (show id j < id i from h), zero_mul]`. Rewrite using `[hB (show id i < id j from h), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem UpperTheory.Reformulated.B.Qk9.tri_diag :
    ∀ {R : Type} [inst : CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R),
    A.BlockTriangular id → B.BlockTriangular id → ∀ (i : Fin n), (A * B) i i = A i i * B i i := by
  intro R _ n A B hA hB i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA (show id j < id i from h), zero_mul]
    · rw [hB (show id i < id j from h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
