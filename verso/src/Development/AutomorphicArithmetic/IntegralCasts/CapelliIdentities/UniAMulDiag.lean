import Mathlib

/- English proof (translation)
Introduce `F _ k A B hA hB i`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[hA (show id j < id i from h), zero_mul]`.

Rewrite using `[hB (show id i < id j from h), mul_zero]`.
-/
theorem UpperTheory.Reformulated.B.Qh23.uniA_mul_diag :
    ∀ {F : Type} [inst : Field F] {k : ℕ} (A B : Matrix (Fin k) (Fin k) F),
    A.BlockTriangular id → B.BlockTriangular id → ∀ (i : Fin k), (A * B) i i = A i i * B i i := by
  intro F _ k A B hA hB i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA (show id j < id i from h), zero_mul]
  · rw [hB (show id i < id j from h), mul_zero]
