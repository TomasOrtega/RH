import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
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
