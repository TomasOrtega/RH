import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Establish `hn1 : ∀ n : ℕ, ‖(n : K)‖ ≤ 1`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Use `push_cast`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))`. Establish `h4 : ‖(4 : K)‖ = 1`. Rewrite using `[show (4 : K) = 2 * 2 by norm_num, norm_mul, h22, one_mul]`. Establish `h4ne : (4 : K) ≠ 0`.

Introduce `h`. Rewrite `h4` using `[h, norm_zero]`. Conclude with `zero_ne_one h4`. Establish `h3n : ‖(3 : K)‖ ≤ 1` using `by simpa using hn1 3`. Establish `h12n : ‖(12 : K)‖ ≤ 1` using `by simpa using hn1 12`.

Establish `h15n : ‖(15 : K)‖ ≤ 1` using `by simpa using hn1 15`. Establish `h36n : ‖(36 : K)‖ ≤ 1` using `by simpa using hn1 36`. Establish `he1 : ‖e‖ ≤ 1`. Assume the negation of the conclusion as `hgt`. Use `push_neg at hgt`.

Establish `hE : 4 * e ^ 3 = g2 * e + g3` using `by linear_combination he`. Establish `hn : ‖(4 : K) * e ^ 3‖ = ‖e‖ ^ 3` using `by rw [norm_mul, h4, one_mul, norm_pow]`. Establish `hle : ‖g2 * e + g3‖ ≤ ‖e‖`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Use polynomial arithmetic with `[norm_nonneg g2, norm_nonneg e]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hle` using `[← hE, hn]`. Establish `hsq : 1 < ‖e‖ ^ 2` using `by nlinarith`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left hsq (by linarith : (0 : ℝ) < ‖e‖)]`.

Use `⟨he1, ?_⟩` and prove the remaining obligations. Establish `hg3 : g3 = 4 * e ^ 3 - g2 * e` using `by linear_combination -he`. Establish `hid : g2 ^ 3 - 27 * g3 ^ 2 = (g2 - 12 * e ^ 2) * (g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4)`. Rewrite using `[hg3]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hk : 3 * e ^ 2 - g2 / 4 = -(g2 - 12 * e ^ 2) / 4`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hen : 0 ≤ ‖e‖` using `norm_nonneg e`. Establish `he2 : ‖e‖ ^ 2 ≤ 1` using `pow_le_one₀ hen he1`.

Establish `he4 : ‖e‖ ^ 4 ≤ 1` using `pow_le_one₀ hen he1`. Establish `hQ : ‖g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4‖ ≤ 1`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) h2`. Rewrite using `[norm_neg, norm_mul, norm_mul, norm_pow]`. Conclude with `mul_le_one₀ (mul_le_one₀ h15n (by positivity) he2) (norm_nonneg _) h2`. Rewrite using `[norm_mul, norm_pow]`.

Conclude with `mul_le_one₀ h36n (by positivity) he4`. Establish `hP : ‖g2 - 12 * e ^ 2‖ ≤ 1`. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)` and prove the remaining obligations. Rewrite using `[norm_neg, norm_mul, norm_pow]`.

Conclude with `mul_le_one₀ h12n (by positivity) he2`. Establish `hP1 : 1 ≤ ‖g2 - 12 * e ^ 2‖`. Use `hΔ` as an intermediate fact. Rewrite `this` using `[hid, norm_mul]`. Use polynomial arithmetic with `[norm_nonneg (g2 - 12 * e ^ 2), norm_nonneg (g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4)]`.

Rewrite using `[hk, norm_div, norm_neg, h4, div_one]`. Conclude with `le_antisymm hP hP1`.
-/
theorem kap_unit {K : Type} [NormedField K] [IsUltrametricDist K] (g2 g3 e : K) (h2 : ‖g2‖ ≤ 1)
    (h3 : ‖g3‖ ≤ 1) (hΔ : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) (h22 : ‖(2 : K)‖ = 1)
    (he : 4 * e ^ 3 - g2 * e - g3 = 0) : ‖e‖ ≤ 1 ∧ ‖3 * e ^ 2 - g2 / 4‖ = 1 := by
  have hn1 : ∀ n : ℕ, ‖(n : K)‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))
  have h4 : ‖(4 : K)‖ = 1 := by
    rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h22, one_mul]
  have h4ne : (4 : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h4
    exact zero_ne_one h4
  have h3n : ‖(3 : K)‖ ≤ 1 := by simpa using hn1 3
  have h12n : ‖(12 : K)‖ ≤ 1 := by simpa using hn1 12
  have h15n : ‖(15 : K)‖ ≤ 1 := by simpa using hn1 15
  have h36n : ‖(36 : K)‖ ≤ 1 := by simpa using hn1 36
  have he1 : ‖e‖ ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    have hE : 4 * e ^ 3 = g2 * e + g3 := by linear_combination he
    have hn : ‖(4 : K) * e ^ 3‖ = ‖e‖ ^ 3 := by rw [norm_mul, h4, one_mul, norm_pow]
    have hle : ‖g2 * e + g3‖ ≤ ‖e‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        nlinarith [norm_nonneg g2, norm_nonneg e]
      · linarith
    rw [← hE, hn] at hle
    have hsq : 1 < ‖e‖ ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left hsq (by linarith : (0 : ℝ) < ‖e‖)]
  refine ⟨he1, ?_⟩
  have hg3 : g3 = 4 * e ^ 3 - g2 * e := by linear_combination -he
  have hid : g2 ^ 3 - 27 * g3 ^ 2 = (g2 - 12 * e ^ 2) * (g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4) := by
    rw [hg3]
    ring
  have hk : 3 * e ^ 2 - g2 / 4 = -(g2 - 12 * e ^ 2) / 4 := by
    field_simp
    ring
  have hen : 0 ≤ ‖e‖ := norm_nonneg e
  have he2 : ‖e‖ ^ 2 ≤ 1 := pow_le_one₀ hen he1
  have he4 : ‖e‖ ^ 4 ≤ 1 := pow_le_one₀ hen he1
  have hQ : ‖g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) h2
      · rw [norm_neg, norm_mul, norm_mul, norm_pow]
        exact mul_le_one₀ (mul_le_one₀ h15n (by positivity) he2) (norm_nonneg _) h2
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ h36n (by positivity) he4
  have hP : ‖g2 - 12 * e ^ 2‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)
    rw [norm_neg, norm_mul, norm_pow]
    exact mul_le_one₀ h12n (by positivity) he2
  have hP1 : 1 ≤ ‖g2 - 12 * e ^ 2‖ := by
    have := hΔ
    rw [hid, norm_mul] at this
    nlinarith [norm_nonneg (g2 - 12 * e ^ 2), norm_nonneg (g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4)]
  rw [hk, norm_div, norm_neg, h4, div_one]
  exact le_antisymm hP hP1

end ReciprocityTheory.ChartRestriction.L1
