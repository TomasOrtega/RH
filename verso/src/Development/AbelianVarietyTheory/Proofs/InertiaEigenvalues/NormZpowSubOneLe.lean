import Mathlib

namespace GlobalTheory.UnitNormPowerSubOne

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Establish `h1` using `IsUltrametricDist.norm_add_le_max (u - 1) (1 : C)`. Rewrite `h1` using `[sub_add_cancel, norm_one]`. Conclude with `h1.trans (max_le h.le le_rfl)`. Establish `h1` using `IsUltrametricDist.norm_add_le_max u (-(u - 1))`.

Establish `e : u + -(u - 1) = 1` using `by ring`. Rewrite `h1` using `[e, norm_one, norm_neg]`. Break down `le_max_iff.mp h1 with h2 | h2` into its components or cases. Conclude with `h2`. Conclude with `absurd h (not_lt.mpr h2)`.
-/
theorem norm_eq_one {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  apply le_antisymm
  · have h1 := IsUltrametricDist.norm_add_le_max (u - 1) (1 : C)
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  · have h1 := IsUltrametricDist.norm_add_le_max u (-(u - 1))
    have e : u + -(u - 1) = 1 := by ring
    rw [e, norm_one, norm_neg] at h1
    rcases le_max_iff.mp h1 with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr h2)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h1` using `IsUltrametricDist.norm_add_le_max (u ^ n * (u - 1)) (u ^ n - 1)`. Establish `e : u ^ n * (u - 1) + (u ^ n - 1) = u ^ (n + 1) - 1` using `by ring`.

Rewrite `h1` using `[e, norm_mul, norm_pow, norm_eq_one u h, one_pow, one_mul]`. Conclude with `h1.trans (max_le le_rfl ih)`.
-/
theorem norm_pow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := IsUltrametricDist.norm_add_le_max (u ^ n * (u - 1)) (u ^ n - 1)
    have e : u ^ n * (u - 1) + (u ^ n - 1) = u ^ (n + 1) - 1 := by ring
    rw [e, norm_mul, norm_pow, norm_eq_one u h, one_pow, one_mul] at h1
    exact h1.trans (max_le le_rfl ih)

/- English proof (translation)
Establish `hn` using `norm_eq_one u h`. Establish `hu : u ≠ 0`. Introduce `h0`. Rewrite `hn` using `[h0, norm_zero]`. Conclude with `zero_ne_one hn`.

Break down `Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩` into its components or cases. Rewrite using `[zpow_natCast]`. Conclude with `norm_pow_sub_one_le u h n`. Establish `hp : u ^ n ≠ 0` using `pow_ne_zero n hu`. Establish `e : u ^ (-(n : ℤ)) - 1 = -((u ^ n)⁻¹ * (u ^ n - 1))`.

Rewrite using `[zpow_neg, zpow_natCast, mul_sub, inv_mul_cancel₀ hp, mul_one, neg_sub]`. Rewrite using `[e, norm_neg, norm_mul, norm_inv, norm_pow, hn, one_pow, inv_one, one_mul]`. Conclude with `norm_pow_sub_one_le u h n`.
-/
theorem norm_zpow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
  have hn := norm_eq_one u h
  have hu : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]
    exact norm_pow_sub_one_le u h n
  · have hp : u ^ n ≠ 0 := pow_ne_zero n hu
    have e : u ^ (-(n : ℤ)) - 1 = -((u ^ n)⁻¹ * (u ^ n - 1)) := by
      rw [zpow_neg, zpow_natCast, mul_sub, inv_mul_cancel₀ hp, mul_one, neg_sub]
    rw [e, norm_neg, norm_mul, norm_inv, norm_pow, hn, one_pow, inv_one, one_mul]
    exact norm_pow_sub_one_le u h n

end GlobalTheory.UnitNormPowerSubOne
