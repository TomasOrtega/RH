import Mathlib

namespace PositivityTheory.RgUd.T2

open Complex Real

/- English proof (translation)
Establish `hup : ∀ n : ℕ, ‖z‖ ^ n ≤ 3 / 2` using `fun n => by`. Establish `h1 : ‖z ^ n‖ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖`. Simplify using `using norm_le_norm_sub_add (z ^ n) 1`. Rewrite `h1` using `[norm_pow]`. Use `h n` as an intermediate fact.

Simplify using `at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlo : ∀ n : ℕ, 1 / 2 ≤ ‖z‖ ^ n` using `fun n => by`. Establish `h1 : ‖(1 : ℂ)‖ ≤ ‖z ^ n‖ + ‖z ^ n - 1‖`. Simplify `norm_le_insert' (1 : ℂ) (z ^ n)` using `[norm_sub_rev]`.

Rewrite `h1` using `[norm_pow]`. Use `h n` as an intermediate fact. Simplify using `at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hz1 : ‖z‖ = 1`.

Break down `lt_trichotomy ‖z‖ 1 with hlt | heq | hgt` into its components or cases. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hlt`. Combine the linear relations using `[hlo n]`. Conclude with `heq`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (3 / 2 : ℝ) hgt`.

Combine the linear relations using `[hup n]`. Establish `hmem : z ∈ Submonoid.unitSphere ℂ`. Simplify `hz1` using `[Submonoid.unitSphere]`. Set `w : Circle` to `(⟨z, hmem⟩ : Submonoid.unitSphere ℂ)`. Establish `hw : (w : ℂ) = z` using `rfl`.

Establish `hw1 : w = 1`. Use `Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_` and prove the remaining obligations. Rewrite using `[Circle.mem_centeredArc (by linarith [pi_pos]), Circle.coe_pow, hw]`. Use `abs_arg_lt_pi_div_two_iff.2 (Or.inl ?_)` and prove the remaining obligations. Establish `h2` using `abs_re_le_norm (z ^ n - 1)`.

Establish `h3` using `h n`. Rewrite `h2` using `[sub_re, one_re]`. Establish `h4` using `neg_abs_le ((z ^ n).re - 1)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← hw, hw1, Circle.coe_one]`.
-/
theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ ≤ 1 / 2) : z = 1 := by

  have hup : ∀ n : ℕ, ‖z‖ ^ n ≤ 3 / 2 := fun n => by
    have h1 : ‖z ^ n‖ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := by
      simpa using norm_le_norm_sub_add (z ^ n) 1
    rw [norm_pow] at h1
    have := h n
    simp at h1
    linarith
  have hlo : ∀ n : ℕ, 1 / 2 ≤ ‖z‖ ^ n := fun n => by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖z ^ n‖ + ‖z ^ n - 1‖ := by
      simpa [norm_sub_rev] using norm_le_insert' (1 : ℂ) (z ^ n)
    rw [norm_pow] at h1
    have := h n
    simp at h1
    linarith
  have hz1 : ‖z‖ = 1 := by
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hlt
      linarith [hlo n]
    · exact heq
    · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 / 2 : ℝ) hgt
      linarith [hup n]
  have hmem : z ∈ Submonoid.unitSphere ℂ := by
    simpa [Submonoid.unitSphere] using hz1
  let w : Circle := (⟨z, hmem⟩ : Submonoid.unitSphere ℂ)
  have hw : (w : ℂ) = z := rfl
  have hw1 : w = 1 := by
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_
    rw [Circle.mem_centeredArc (by linarith [pi_pos]), Circle.coe_pow, hw]
    refine abs_arg_lt_pi_div_two_iff.2 (Or.inl ?_)
    have h2 := abs_re_le_norm (z ^ n - 1)
    have h3 := h n
    rw [sub_re, one_re] at h2
    have h4 := neg_abs_le ((z ^ n).re - 1)
    linarith
  rw [← hw, hw1, Circle.coe_one]

end PositivityTheory.RgUd.T2
