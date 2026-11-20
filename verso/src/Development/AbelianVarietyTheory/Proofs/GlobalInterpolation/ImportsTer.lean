import Mathlib

namespace GlobalTheory.IterationConvergence

/- English proof (translation)
Establish `e : w ^ 2 - 1 = (w - 1) * (w + 1)` using `by ring`. Establish `e2 : w + 1 = 2 - (1 - w)` using `by ring`. Establish `h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖`. Use `norm_sub_norm_le (2 : ℂ) (1 - w)` as an intermediate fact. Rewrite `this` using `[← e2]`.

Establish `h1 : ‖(1 : ℂ) - w‖ = ‖w - 1‖` using `norm_sub_rev _ _`. Establish `h3 : ‖(2 : ℂ)‖ = 2` using `by simp`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e, norm_mul]`. Rewrite using `[mul_comm]`.

Conclude with `mul_le_mul_of_nonneg_left h2 (norm_nonneg _)`.
-/
theorem step (w : ℂ) (h : ‖w - 1‖ < 1 / 2) : (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have e2 : w + 1 = 2 - (1 - w) := by ring
  have h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
    have := norm_sub_norm_le (2 : ℂ) (1 - w)
    rw [← e2] at this
    have h1 : ‖(1 : ℂ) - w‖ = ‖w - 1‖ := norm_sub_rev _ _
    have h3 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  rw [e, norm_mul]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `hs` using `step (z ^ (2 ^ k)) (hz _)`. Establish `e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2`.

Rewrite using `[← pow_mul, pow_succ]`. Rewrite using `[e, pow_succ]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem iter {z : ℂ} (hz : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := step (z ^ (2 ^ k)) (hz _)
    have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [e, pow_succ]
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = (3 / 2) * ((3 / 2) ^ k * ‖z - 1‖) := by ring
      _ ≤ (3 / 2) * ‖z ^ (2 ^ k) - 1‖ := by gcongr
      _ ≤ _ := hs

/- English proof (translation)
Introduce `z hz`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖z - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hne)`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)`. Establish `h1` using `iter hz k`.

Establish `h2` using `hz (2 ^ k)`. Rewrite `hk` using `[div_lt_iff₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := iter hz k
  have h2 := hz (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.IterationConvergence
