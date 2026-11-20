import Mathlib

open Finset

namespace GlobalTheory.LamSize

/- English proof (translation)
Introduce `C b T T' r N hC hb hN hT hT'`. Establish `hm1 : 1 ≤ 2 * r + 2` using `by omega`. Generalize the expression as in `2 * r + 2 = m at *`. Establish `hb0 : 0 < b` using `by linarith`. Establish `hb1 : 1 ≤ b` using `by linarith`.

Establish `hm0 : (0 : ℝ) ≤ (m : ℝ)` using `Nat.cast_nonneg m`. Use `⟨Real.one_le_rpow hb1 (by positivity), ?_⟩` and prove the remaining obligations. Establish `hp : 0 < b ^ (-(C * (m : ℝ)))` using `Real.rpow_pos_of_pos hb0 _`. Establish `hTT : b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))) ≤ T * T'` using `mul_le_mul hT hT' hp.le (hp.le.trans hT)`. Establish `key : (b ^ ((6 + C) * (m : ℝ))) ^ 2 * (b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ)))) = b ^ (12 * m)`.

Rewrite using `[sq, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_natCast]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.
-/
theorem main : ∀ (C b T T' : ℝ) (r N : ℕ), 0 ≤ C → 3 ≤ b → (N : ℝ) ≤ b → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T' → 1 ≤ b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ)) ∧ (N : ℝ) * b ^ (11 * (2 * r + 2)) ≤ (b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 * (T * T') := by
  intro C b T T' r N hC hb hN hT hT'
  have hm1 : 1 ≤ 2 * r + 2 := by omega
  generalize 2 * r + 2 = m at *
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine ⟨Real.one_le_rpow hb1 (by positivity), ?_⟩
  have hp : 0 < b ^ (-(C * (m : ℝ))) := Real.rpow_pos_of_pos hb0 _
  have hTT : b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))) ≤ T * T' :=
    mul_le_mul hT hT' hp.le (hp.le.trans hT)
  have key : (b ^ ((6 + C) * (m : ℝ))) ^ 2 * (b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))))
      = b ^ (12 * m) := by
    rw [sq, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  calc (N : ℝ) * b ^ (11 * m) ≤ b * b ^ (11 * m) := by gcongr
    _ = b ^ (11 * m + 1) := by ring
    _ ≤ b ^ (12 * m) := pow_le_pow_right₀ hb1 (by omega)
    _ = _ := key.symm
    _ ≤ _ := by gcongr

end GlobalTheory.LamSize
