import Mathlib

namespace GlobalTheory.CompanionTheory.Casselman

/- English proof (translation)
Introduce `δ r hδ hr h`. Establish `h2 : (Real.sqrt δ * r) ^ (2 : ℝ) = δ * r ^ 2`. Rewrite using `[Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le]`. Rewrite `h` using `[h2, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one :
    ∀ (δ r : ℝ), 0 < δ → 0 ≤ r → δ⁻¹ * (Real.sqrt δ * r) ^ (2 : ℝ) < 1 → r < 1 := by
  intro δ r hδ hr h
  have h2 : (Real.sqrt δ * r) ^ (2 : ℝ) = δ * r ^ 2 := by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le]
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul] at h
  nlinarith

end GlobalTheory.CompanionTheory.Casselman
