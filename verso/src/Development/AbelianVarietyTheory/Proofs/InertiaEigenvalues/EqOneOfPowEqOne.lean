import Mathlib

universe u_1

namespace GlobalTheory.PowerEqOneClose

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : u ^ (n + 1) - 1 = (u ^ n - 1) * u + (u - 1)` using `by ring`. Rewrite using `[e]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) hu).trans ih`.
-/
theorem norm_pow_sub_one_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] (u : K)
    (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = (u ^ n - 1) * u + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hu).trans ih

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : K) = ((∑ i ∈ Finset.range n, u ^ i) - (n : K)) + (u ^ n - 1)`. Rewrite using `[Finset.sum_range_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (norm_pow_sub_one_le u hu n))`.
-/
theorem norm_geom_sum_sub_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] (u : K)
    (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖(∑ i ∈ Finset.range n, u ^ i) - (n : K)‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : K)
        = ((∑ i ∈ Finset.range n, u ^ i) - (n : K)) + (u ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ih (norm_pow_sub_one_le u hu n))

/- English proof (translation)
Establish `hu1 : ‖u‖ ≤ 1`. Establish `e : u = (u - 1) + 1` using `by ring`. Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.le norm_one.le)`. Establish `hs` using `norm_geom_sum_sub_le u hu1 m`.

Establish `hg : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0`. Rewrite using `[geom_sum_mul, hu, sub_self]`. Break down `mul_eq_zero.mp hg with h0 | h0` into its components or cases. Rewrite `hs` using `[h0, zero_sub, norm_neg, hm]`. Conclude with `absurd h (not_lt.mpr hs)`.

Conclude with `sub_eq_zero.mp h0`.
-/
theorem eq_one_of_pow_eq_one {K : Type u_1} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (hm : ‖(m : K)‖ = (1 : ℝ)) (u : K) (hu : u ^ m = (1 : K)) (h : ‖u - (1 : K)‖ < (1 : ℝ)) :
    u = (1 : K) := by
  have hu1 : ‖u‖ ≤ 1 := by
    have e : u = (u - 1) + 1 := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.le norm_one.le)
  have hs := norm_geom_sum_sub_le u hu1 m
  have hg : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu, sub_self]
  rcases mul_eq_zero.mp hg with h0 | h0
  · rw [h0, zero_sub, norm_neg, hm] at hs
    exact absurd h (not_lt.mpr hs)
  · exact sub_eq_zero.mp h0

end GlobalTheory.PowerEqOneClose
