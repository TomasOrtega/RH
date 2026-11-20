import Mathlib

/- English proof (translation)
Establish `hw : w ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`. Establish `e : w⁻¹ - 1 = (1 - w) / w` using `by field_simp`. Rewrite `h` using `[e, norm_div, div_lt_one (norm_pos_iff.mpr hw)]`.

Establish `h2 : ‖1 - w‖ ^ 2 < ‖w‖ ^ 2`. Use `norm_nonneg (1 - w)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite `h2` using `[Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]`. Simplify using `only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at h2`.

Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem UpperTheory.Reformulated.B.Qk23.half_le_re {w : ℂ} (h : ‖w⁻¹ - 1‖ < 1) : (1 / 2 : ℝ) ≤ w.re := by
  have hw : w ≠ 0 := by
    rintro rfl
    simp at h
  have e : w⁻¹ - 1 = (1 - w) / w := by field_simp
  rw [e, norm_div, div_lt_one (norm_pos_iff.mpr hw)] at h
  have h2 : ‖1 - w‖ ^ 2 < ‖w‖ ^ 2 := by
    have := norm_nonneg (1 - w)
    nlinarith
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at h2
  nlinarith

/- English proof (translation)
Introduce `z h`. Assume the negation of the conclusion as `hz`. Establish `hd : 0 < ‖z - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hz)`. Establish `hre : ∀ k : ℕ, (1 / 2 : ℝ) ≤ (z ^ k).re`. Introduce `k`.

Apply `UpperTheory.Reformulated.B.Qk23.half_le_re` to reduce the goal to its premises. Use `h (-(k : ℤ))` as an intermediate fact. Rewrite `this` using `[zpow_neg, zpow_natCast]`. Then use the resulting hypothesis. Take `⟨n, hn⟩` from `exists_nat_gt (2 / ‖z - 1‖)`. Rewrite `hn` using `[div_lt_iff₀ hd]`.

Establish `h1 : (n : ℝ) * (1 / 2) ≤ ‖∑ k ∈ Finset.range n, z ^ k‖`. Use `le_trans ?_ (Complex.re_le_norm _)` and prove the remaining obligations. Rewrite using `[Complex.re_sum]`. Use `Finset.card_nsmul_le_sum (Finset.range n) (fun k => (z ^ k).re) (1 / 2 : ℝ) (fun k _ => hre k)` as an intermediate fact. Rewrite `this` using `[Finset.card_range, nsmul_eq_mul]`. Then use the resulting hypothesis.

Establish `h2 : ‖∑ k ∈ Finset.range n, z ^ k‖ * ‖z - 1‖ < 1`. Rewrite using `[← norm_mul, geom_sum_mul]`. Use `h (n : ℤ)` as an intermediate fact. Rewrite `this` using `[zpow_natCast]`. Then use the resulting hypothesis. Establish `h3` using `mul_le_mul_of_nonneg_right h1 hd.le`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow :
    ∀ {z : ℂ}, (∀ (k : ℤ), ‖z ^ k - (1 : ℂ)‖ < (1 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hz
  have hd : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hre : ∀ k : ℕ, (1 / 2 : ℝ) ≤ (z ^ k).re := by
    intro k
    apply UpperTheory.Reformulated.B.Qk23.half_le_re
    have := h (-(k : ℤ))
    rwa [zpow_neg, zpow_natCast] at this
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ‖z - 1‖)
  rw [div_lt_iff₀ hd] at hn
  have h1 : (n : ℝ) * (1 / 2) ≤ ‖∑ k ∈ Finset.range n, z ^ k‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have := Finset.card_nsmul_le_sum (Finset.range n) (fun k => (z ^ k).re) (1 / 2 : ℝ)
      (fun k _ => hre k)
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have h2 : ‖∑ k ∈ Finset.range n, z ^ k‖ * ‖z - 1‖ < 1 := by
    rw [← norm_mul, geom_sum_mul]
    have := h (n : ℤ)
    rwa [zpow_natCast] at this
  have h3 := mul_le_mul_of_nonneg_right h1 hd.le
  linarith
