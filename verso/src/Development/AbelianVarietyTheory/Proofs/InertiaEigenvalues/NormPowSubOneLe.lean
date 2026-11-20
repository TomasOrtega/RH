import Mathlib

namespace GlobalTheory.CloseToUnitNorm

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Establish `h1` using `IsUltrametricDist.norm_add_le_max (u - 1) (1 : C)`. Rewrite `h1` using `[sub_add_cancel, norm_one]`. Conclude with `h1.trans (max_le h.le le_rfl)`. Establish `h1` using `IsUltrametricDist.norm_add_le_max u (1 - u)`.

Rewrite `h1` using `[add_sub_cancel, norm_one, norm_sub_rev]`. Break down `le_max_iff.mp h1 with h2 | h2` into its components or cases. Conclude with `h2`. Conclude with `absurd h (not_lt.mpr h2)`.
-/
theorem norm_eq_one_of_close {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  apply le_antisymm
  · have h1 := IsUltrametricDist.norm_add_le_max (u - 1) (1 : C)
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  · have h1 := IsUltrametricDist.norm_add_le_max u (1 - u)
    rw [add_sub_cancel, norm_one, norm_sub_rev] at h1
    rcases le_max_iff.mp h1 with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr h2)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1)` using `by ring`. Rewrite using `[e]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)` and prove the remaining obligations. Rewrite using `[norm_mul, hu, one_mul]`. Conclude with `ih`.
-/
theorem norm_pow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (hu : ‖u‖ = 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hu, one_mul]
    exact ih

/- English proof (translation)
Establish `hu : ‖u‖ = 1` using `norm_eq_one_of_close u h`. Establish `hu0 : u ≠ 0`. Introduce `h0`. Rewrite `hu` using `[h0, norm_zero]`. Conclude with `zero_ne_one hu`.

Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg i`. Rewrite using `[zpow_natCast]`. Conclude with `norm_pow_sub_one_le u hu n`. Rewrite using `[zpow_neg, zpow_natCast]`. Establish `hn : u ^ n ≠ 0` using `pow_ne_zero n hu0`.

Establish `e : (u ^ n)⁻¹ - 1 = -((u ^ n)⁻¹ * (u ^ n - 1))`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_neg, norm_mul, norm_inv, norm_pow, hu, one_pow, inv_one, one_mul]`. Conclude with `norm_pow_sub_one_le u hu n`.
-/
theorem norm_zpow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - (1 : C)‖ < (1 : ℝ)) (i : ℤ) : ‖u ^ i - (1 : C)‖ ≤ ‖u - (1 : C)‖ := by
  have hu : ‖u‖ = 1 := norm_eq_one_of_close u h
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact zero_ne_one hu
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · rw [zpow_natCast]
    exact norm_pow_sub_one_le u hu n
  · rw [zpow_neg, zpow_natCast]
    have hn : u ^ n ≠ 0 := pow_ne_zero n hu0
    have e : (u ^ n)⁻¹ - 1 = -((u ^ n)⁻¹ * (u ^ n - 1)) := by
      field_simp
      ring
    rw [e, norm_neg, norm_mul, norm_inv, norm_pow, hu, one_pow, inv_one, one_mul]
    exact norm_pow_sub_one_le u hu n

end GlobalTheory.CloseToUnitNorm
