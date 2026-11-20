import Mathlib

namespace GlobalTheory.StrictUpperNilpotentFlagMeasures

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `i j h`. Rewrite using `[pow_zero]`. Apply `Matrix.one_apply_ne` to reduce the goal to its premises.

Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`. Introduce `i j h`. Rewrite using `[pow_succ, Matrix.mul_apply]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : (k : ℕ) < (i : ℕ) + n`. Rewrite using `[ih i k hk, zero_mul]`. Rewrite using `[hX k j (by omega), mul_zero]`.
-/
theorem pow_apply_eq_zero_of_strictUpper {m : ℕ} {X : Matrix (Fin m) (Fin m) ℂ}
    (hX : ∀ i j : Fin m, (j : ℕ) ≤ (i : ℕ) → X i j = 0) (n : ℕ) :
    ∀ i j : Fin m, (j : ℕ) < (i : ℕ) + n → (X ^ n) i j = 0 := by
  induction n with
  | zero =>
    intro i j h
    rw [pow_zero]
    apply Matrix.one_apply_ne
    rintro rfl
    omega
  | succ n ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) < (i : ℕ) + n
    · rw [ih i k hk, zero_mul]
    · rw [hX k j (by omega), mul_zero]

end GlobalTheory.StrictUpperNilpotentFlagMeasures
