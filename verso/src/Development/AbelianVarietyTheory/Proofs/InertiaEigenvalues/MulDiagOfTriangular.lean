import Mathlib

namespace GlobalTheory.TriangularDiagonal

/- English proof (translation)
Introduce `p κ hκ M N hM hN i`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i ?_ ?_` and prove the remaining obligations. Introduce `k _ hk`. Break down `lt_trichotomy (κ i) (κ k) with h | h | h` into its components or cases.

Rewrite using `[hM i k h, zero_mul]`. Conclude with `absurd (hκ h).symm hk`. Rewrite using `[hN k i h, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem mul_diag_of_triangular :
    ∀ {p : ℕ} {κ : Fin p → ℤ}, Function.Injective κ → ∀ {M N : Matrix (Fin p) (Fin p) ℂ},
      (∀ (a b : Fin p), κ a < κ b → M a b = (0 : ℂ)) →
      (∀ (a b : Fin p), κ a < κ b → N a b = (0 : ℂ)) →
      ∀ (i : Fin p), (M * N) i i = M i i * N i i := by
  intro p κ hκ M N hM hN i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hk
    rcases lt_trichotomy (κ i) (κ k) with h | h | h
    · rw [hM i k h, zero_mul]
    · exact absurd (hκ h).symm hk
    · rw [hN k i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

end GlobalTheory.TriangularDiagonal
