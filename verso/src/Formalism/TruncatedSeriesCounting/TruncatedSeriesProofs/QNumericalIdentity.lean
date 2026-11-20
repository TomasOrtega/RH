import Mathlib
import Formalism.TruncatedSeriesCounting.StatementX

namespace Formalism.TruncatedSeriesCounting.X

/- English proof (authored)
Put d = ℓ−1 > 0. The natural-number quotient H′ / (ℓ−1) is at most H′/d in the reals. Combine it with the rational term in the bound on eW to get H′/d + H′ℓ/d² = H′(2ℓ−1)/d². This is at most H(2ℓ−1)/d² because H′ ≤ H.

If H is positive, H′+1 ≤ 2H, so log base ℓ of H′+1 is at most log base ℓ of 2H. If H = 0, then H′ = 0 and the logarithmic bound with the added 1 holds under Lean’s real logarithm convention. Substitute these bounds, cancel the +1 and −1 from the left side, and use the definition of aR.
-/
theorem q_numerical_identity : QaNum := by
  intro ℓ hℓ H' H eW hH heW
  unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hd : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hdiv : ((H' / (ℓ - 1) : ℕ) : ℝ) ≤ (H' : ℝ) / ((ℓ : ℝ) - 1) := by
    have h := Nat.cast_div_le (m := H') (n := ℓ - 1) (α := ℝ)
    rwa [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one] at h
  have hlog : Real.logb ℓ ((H' : ℝ) + 1) ≤ Real.logb ℓ (2 * (H : ℝ)) + 1 := by
    rcases Nat.eq_zero_or_pos H with h0 | hpos
    · subst h0
      have h0' : H' = 0 := by omega
      subst h0'
      simp
    · have h1 : (H' : ℝ) + 1 ≤ 2 * H := by
        have h2 : (H' : ℝ) ≤ H := by exact_mod_cast hH
        have h3 : (1 : ℝ) ≤ H := by exact_mod_cast hpos
        linarith
      have h4 := Real.logb_le_logb_of_le hℓ1 (by positivity) h1
      linarith
  have hfrac : (H' : ℝ) / ((ℓ : ℝ) - 1) + (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤
      (H : ℝ) * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    have heq : (H' : ℝ) / ((ℓ : ℝ) - 1) + (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
        (H' : ℝ) * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
      have := hd.ne'
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ (pow_pos hd 2).le
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hH) (by linarith)
  push_cast
  linarith

end Formalism.TruncatedSeriesCounting.X
