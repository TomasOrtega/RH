import Mathlib

/- English proof (translation)
Introduce `n Q _ a b ha hb i`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[hb j i h, mul_zero]`.

Rewrite using `[ha i j h, zero_mul]`.
-/
theorem UpperTheory.Reformulated.B.Qk64.diag_mul :
    ∀ {n : ℕ} {Q : Type} [inst : CommRing Q]
    (a b : Matrix (Fin n) (Fin n) Q),
    (∀ (i j : Fin n), i < j → a i j = (0 : Q)) →
      (∀ (i j : Fin n), i < j → b i j = (0 : Q)) → ∀ (i : Fin n), (a * b) i i = a i i * b i i := by
  intro n Q _ a b ha hb i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hb j i h, mul_zero]
  · rw [ha i j h, zero_mul]
