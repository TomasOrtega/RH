import Mathlib

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

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
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

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
