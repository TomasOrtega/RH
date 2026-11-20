import Mathlib

universe u_1 u_2

namespace GlobalTheory.ValuationPowSubPow

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b)` using `by ring`. Rewrite using `[h]`.

Use `w.map_add_le ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `(mul_le_of_le_one_left' ha).trans ih`. Rewrite using `[map_mul, map_pow]`. Conclude with `mul_le_of_le_one_left' (pow_le_one' hb n)`.
-/
theorem valuation_pow_sub_pow_le {K : Type u_1} {Γ : Type u_2} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {a b : K}
    (ha : w a ≤ 1) (hb : w b ≤ 1) (m : ℕ) : w (a ^ m - b ^ m) ≤ w (a - b) := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by ring
    rw [h]
    refine w.map_add_le ?_ ?_
    · rw [map_mul]
      exact (mul_le_of_le_one_left' ha).trans ih
    · rw [map_mul, map_pow]
      exact mul_le_of_le_one_left' (pow_le_one' hb n)

end GlobalTheory.ValuationPowSubPow
