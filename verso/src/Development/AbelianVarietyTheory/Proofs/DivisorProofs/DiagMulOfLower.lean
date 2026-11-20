import Mathlib

namespace GlobalTheory.DiagonalTimesLowerTriangular

/- English proof (translation)
Introduce `i`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i ?_ ?_` and prove the remaining obligations. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases.

Rewrite using `[hb k i h, mul_zero]`. Rewrite using `[ha i k h, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem diag_mul_of_lower {K : Type} [CommRing K] {s : ℕ} {a b : Matrix (Fin s) (Fin s) K}
    (ha : ∀ (i j : Fin s), i < j → a i j = (0 : K))
    (hb : ∀ (i j : Fin s), i < j → b i j = (0 : K)) :
    ∀ (i : Fin s), (a * b) i i = a i i * b i i := by
  intro i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hb k i h, mul_zero]
    · rw [ha i k h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Introduce `ha hb` and use `diag_mul_of_lower ha hb`.
-/
theorem main : ∀ {K : Type} [inst : CommRing K] {s : ℕ} {a b : Matrix (Fin s) (Fin s) K}, (∀ (i j : Fin s), i < j → a i j = (0 : K)) → (∀ (i j : Fin s), i < j → b i j = (0 : K)) → ∀ (i : Fin s), (a * b) i i = a i i * b i i :=
  fun ha hb => diag_mul_of_lower ha hb

end GlobalTheory.DiagonalTimesLowerTriangular
