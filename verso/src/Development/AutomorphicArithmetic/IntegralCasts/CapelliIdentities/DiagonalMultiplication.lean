import Mathlib

/- English proof (translation)
Introduce `R _ X Y hX hY a`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single a (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ a) h)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hb with h | h` into its components or cases. Rewrite using `[hX a b h, zero_mul]`.

Rewrite using `[hY b a h, mul_zero]`.
-/
theorem UpperTheory.Reformulated.B.UpperTriangularThreeDiagonalOfMul.diag_mul :
    ∀ {R : Type} [inst : CommRing R]
    (X Y : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R),
    (∀ (i j : Fin (3 : ℕ)), j < i → X i j = (0 : R)) →
      (∀ (i j : Fin (3 : ℕ)), j < i → Y i j = (0 : R)) → ∀ (a : Fin (3 : ℕ)), (X * Y) a a = X a a * Y a a := by
  intro R _ X Y hX hY a
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single a (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ a) h)
  rcases lt_or_gt_of_ne hb with h | h
  · rw [hX a b h, zero_mul]
  · rw [hY b a h, mul_zero]
