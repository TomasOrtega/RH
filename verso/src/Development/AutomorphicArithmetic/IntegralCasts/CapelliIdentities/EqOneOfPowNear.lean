import Mathlib

/- English proof (translation)
Introduce `z h`. Establish `step : ∀ n : ℕ, (3 / 2 : ℝ) * ‖z ^ n - 1‖ ≤ ‖z ^ (n * 2) - 1‖`. Introduce `n`. Establish `e : z ^ (n * 2) - 1 = (z ^ n + 1) * (z ^ n - 1)` using `by ring`. Establish `h1 : ‖(2 : ℂ)‖ ≤ ‖z ^ n + 1‖ + ‖z ^ n - 1‖`.

Establish `e2 : (2 : ℂ) = (z ^ n + 1) - (z ^ n - 1)` using `by ring`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ‖(2 : ℂ)‖ = 2` using `by simp`. Establish `h3` using `h n`. Rewrite using `[e, norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)`. Establish `grow : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Establish `s` using `step (2 ^ k)`. Rewrite using `[pow_succ, pow_succ]`. Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hz`.

Establish `hpos : 0 < ‖z - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hz)`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)`. Rewrite `hk` using `[div_lt_iff₀ hpos]`. Establish `g` using `grow k`. Establish `h4` using `h (2 ^ k)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near :
    ∀ (z : ℂ),
    (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have step : ∀ n : ℕ, (3 / 2 : ℝ) * ‖z ^ n - 1‖ ≤ ‖z ^ (n * 2) - 1‖ := by
    intro n
    have e : z ^ (n * 2) - 1 = (z ^ n + 1) * (z ^ n - 1) := by ring
    have h1 : ‖(2 : ℂ)‖ ≤ ‖z ^ n + 1‖ + ‖z ^ n - 1‖ := by
      have e2 : (2 : ℂ) = (z ^ n + 1) - (z ^ n - 1) := by ring
      calc ‖(2 : ℂ)‖ = ‖(z ^ n + 1) - (z ^ n - 1)‖ := congrArg _ e2
        _ ≤ _ := norm_sub_le _ _
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have h3 := h n
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have grow : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have s := step (2 ^ k)
      rw [pow_succ, pow_succ]
      linarith
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ hpos] at hk
  have g := grow k
  have h4 := h (2 ^ k)
  linarith
