import Mathlib

namespace UpperTheory.Reformulated.B.P6.r25a

/- English proof (translation)
Establish `h1 : w ^ 2 - 1 = (w - 1) * (w + 1)` using `by ring`. Establish `h2 : (w + 1) - (w - 1) = (2 : ℂ)` using `by ring`. Establish `h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖`. Establish `h` using `norm_sub_le (w + 1) (w - 1)`. Rewrite `h` using `[h2]`. Then use the resulting hypothesis.

Establish `h4 : ‖(2 : ℂ)‖ = 2` using `by simp`. Establish `h5 : (3 / 2 : ℝ) ≤ ‖w + 1‖` using `by linarith`. Establish `h6 : 0 ≤ ‖w - 1‖` using `norm_nonneg _`. Establish `h7 : ‖w - 1‖ * (3 / 2) ≤ ‖w - 1‖ * ‖w + 1‖` using `mul_le_mul_of_nonneg_left h5 h6`. Rewrite using `[h1, norm_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sq_sub_one_lower_bound (w : ℂ) (hw : ‖w - 1‖ < 1 / 2) :
    (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have h1 : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (w + 1) - (w - 1) = (2 : ℂ) := by ring
  have h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have h := norm_sub_le (w + 1) (w - 1)
    rwa [h2] at h
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  have h5 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by linarith
  have h6 : 0 ≤ ‖w - 1‖ := norm_nonneg _
  have h7 : ‖w - 1‖ * (3 / 2) ≤ ‖w - 1‖ * ‖w + 1‖ := mul_le_mul_of_nonneg_left h5 h6
  rw [h1, norm_mul]
  linarith

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2`.

Rewrite using `[← pow_mul, ← pow_succ]`. Establish `hs` using `sq_sub_one_lower_bound (z ^ (2 ^ k)) (hz _)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pow_two_pow_sub_one_growth (z : ℂ) (hz : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) :
    ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    have hs := sq_sub_one_lower_bound (z ^ (2 ^ k)) (hz _)
    calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = (3 / 2) * ((3 / 2) ^ k * ‖z - 1‖) := by ring
      _ ≤ (3 / 2) * ‖z ^ (2 ^ k) - 1‖ := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ ‖(z ^ (2 ^ k)) ^ 2 - 1‖ := hs
      _ = ‖z ^ (2 ^ (k + 1)) - 1‖ := by rw [e]

/- English proof (translation)
Introduce `z hz`. Establish `hz' : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2` using `hz`. Establish `hstep` using `pow_two_pow_sub_one_growth z hz'`. Establish `hd : ‖z - 1‖ = 0`. Assume the negation of the conclusion as `hne`.

Establish `hpos : 0 < ‖z - 1‖` using `lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)`. Establish `h1` using `hstep k`. Establish `h2` using `hz' (2 ^ k)`. Establish `h2d : (0 : ℝ) < 2 * ‖z - 1‖` using `by positivity`.

Rewrite `hk` using `[div_lt_iff₀ h2d]`. Establish `h3 : (3 / 2 : ℝ) ^ k * (2 * ‖z - 1‖) = 2 * ((3 / 2) ^ k * ‖z - 1‖)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hz1 : z - 1 = 0` using `norm_eq_zero.mp hd`. Conclude with `sub_eq_zero.mp hz1`.
-/
theorem Tw.HeisLatVac.lc_pow_near_one :
    ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - OfNat.ofNat (nat_lit 1)‖ < OfNat.ofNat (nat_lit 1) / OfNat.ofNat (nat_lit 2)) → z = OfNat.ofNat (nat_lit 1) := by
  intro z hz
  have hz' : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2 := hz
  have hstep := pow_two_pow_sub_one_growth z hz'
  have hd : ‖z - 1‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖z - 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
    have h1 := hstep k
    have h2 := hz' (2 ^ k)
    have h2d : (0 : ℝ) < 2 * ‖z - 1‖ := by positivity
    rw [div_lt_iff₀ h2d] at hk
    have h3 : (3 / 2 : ℝ) ^ k * (2 * ‖z - 1‖) = 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
    linarith
  have hz1 : z - 1 = 0 := norm_eq_zero.mp hd
  exact sub_eq_zero.mp hz1

end UpperTheory.Reformulated.B.P6.r25a
