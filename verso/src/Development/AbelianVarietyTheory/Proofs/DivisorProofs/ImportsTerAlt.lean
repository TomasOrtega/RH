import Mathlib

namespace GlobalTheory.IterativeScalingBound

/- English proof (translation)
Establish `e : w ^ 2 - 1 = (w - 1) * (2 + (w - 1))` using `by ring`. Rewrite using `[e, norm_mul]`. Establish `h2 : (3/2 : ℝ) ≤ ‖2 + (w - 1)‖`. Establish `t` using `norm_sub_le (2 + (w - 1)) (w - 1)`. Establish `e2 : (2 + (w - 1)) - (w - 1) = (2 : ℂ)` using `by ring`.

Rewrite `t` using `[e2]`. Establish `: ‖(2 : ℂ)‖ = 2` using `by simp`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0 : 0 ≤ ‖w - 1‖` using `norm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w - 1) * (2 + (w - 1)) := by ring
  rw [e, norm_mul]
  have h2 : (3/2 : ℝ) ≤ ‖2 + (w - 1)‖ := by
    have t := norm_sub_le (2 + (w - 1)) (w - 1)
    have e2 : (2 + (w - 1)) - (w - 1) = (2 : ℂ) := by ring
    rw [e2] at t
    have : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  have h0 : 0 ≤ ‖w - 1‖ := norm_nonneg _
  nlinarith

/- English proof (translation)
Introduce `z h`. Establish `key : ∀ k : ℕ, (3/2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ 2 ^ k - 1‖`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Establish `e : z ^ 2 ^ (n + 1) = (z ^ 2 ^ n) ^ 2` using `by rw [pow_succ 2 n, pow_mul]`. Rewrite using `[e, pow_succ (3/2 : ℝ) n]`. Combine the equalities or inequalities in the displayed calculation. Assume the negation of the conclusion as `hne`.

Establish `hpos : 0 < ‖z - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hne)`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)`. Establish `h1` using `key k`. Establish `h2` using `h k`. Establish `h3 : 1 / 2 < (3/2 : ℝ) ^ k * ‖z - 1‖` using `by rwa [div_lt_iff₀ hpos] at hk`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : ∀ (z : ℂ), (∀ (k : ℕ), ‖z ^ (2 : ℕ) ^ k - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have key : ∀ k : ℕ, (3/2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ 2 ^ k - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have e : z ^ 2 ^ (n + 1) = (z ^ 2 ^ n) ^ 2 := by rw [pow_succ 2 n, pow_mul]
      rw [e, pow_succ (3/2 : ℝ) n]
      calc (3/2 : ℝ) ^ n * (3/2) * ‖z - 1‖ = (3/2) * ((3/2) ^ n * ‖z - 1‖) := by ring
        _ ≤ (3/2) * ‖z ^ 2 ^ n - 1‖ := by gcongr
        _ ≤ _ := step _ (h n)
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key k
  have h2 := h k
  have h3 : 1 / 2 < (3/2 : ℝ) ^ k * ‖z - 1‖ := by rwa [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.IterativeScalingBound
