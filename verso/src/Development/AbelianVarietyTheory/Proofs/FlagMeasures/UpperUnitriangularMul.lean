import Mathlib

namespace GlobalTheory.UpperUnitriangularMul

open Matrix

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b hba`. Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c _`.

Break down `lt_or_ge c a with h | h` into its components or cases. Rewrite using `[hU a c h, zero_mul]`. Rewrite using `[hW c b (lt_of_lt_of_le hba h), mul_zero]`. Introduce `a`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a]`.

Rewrite using `[hU1, hW1, one_mul]`. Introduce `c _ hca`. Break down `lt_or_gt_of_ne hca with h | h` into its components or cases. Rewrite using `[hU a c h, zero_mul]`. Rewrite using `[hW c a h, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ a) h`.
-/
theorem upperUnitriangular_mul {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    {U W : Matrix (Fin N) (Fin N) E}
    (hU : ∀ a b : Fin N, b < a → U a b = (0 : E)) (hU1 : ∀ a : Fin N, U a a = (1 : E))
    (hW : ∀ a b : Fin N, b < a → W a b = (0 : E)) (hW1 : ∀ a : Fin N, W a a = (1 : E)) :
    (∀ a b : Fin N, b < a → (U * W) a b = (0 : E)) ∧ ∀ a : Fin N, (U * W) a a = (1 : E) := by
  constructor
  · intro a b hba
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    rcases lt_or_ge c a with h | h
    · rw [hU a c h, zero_mul]
    · rw [hW c b (lt_of_lt_of_le hba h), mul_zero]
  · intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hU1, hW1, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hU a c h, zero_mul]
      · rw [hW c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.UpperUnitriangularMul
