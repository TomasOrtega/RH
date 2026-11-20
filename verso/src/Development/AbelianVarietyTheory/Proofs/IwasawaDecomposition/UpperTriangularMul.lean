import Mathlib

namespace GlobalTheory.UpperTriangularMul

/- English proof (translation)
Introduce `n R _ M N hM hN`. Use `⟨fun a i hia => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Break down `lt_or_ge j a with h | h` into its components or cases.

Rewrite using `[hM a j h, zero_mul]`. Rewrite using `[hN j i (lt_of_lt_of_le hia h), mul_zero]`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hji with h | h` into its components or cases.

Rewrite using `[hM i j h, zero_mul]`. Rewrite using `[hN j i h, mul_zero]`.
-/
theorem upperTriangular_mul :
    ∀ {n : ℕ} {R : Type} [inst : CommRing R] {M N : Matrix (Fin n) (Fin n) R},
      (∀ (a i : Fin n), i < a → M a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → N a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → (M * N) a i = (0 : R)) ∧
        ∀ (i : Fin n), (M * N) i i = M i i * N i i := by
  intro n R _ M N hM hN
  refine ⟨fun a i hia => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j a with h | h
    · rw [hM a j h, zero_mul]
    · rw [hN j i (lt_of_lt_of_le hia h), mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hM i j h, zero_mul]
    · rw [hN j i h, mul_zero]

end GlobalTheory.UpperTriangularMul
