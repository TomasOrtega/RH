import Mathlib

namespace GlobalTheory.PowerTwoNormLowerBound

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => set w := z ^ (2 ^ k) with hw`. Establish `hw1 : ‖w - 1‖ < 1 / 2` using `h _`.

Establish `h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖`. Establish `e : (2 : ℂ) = (w + 1) - (w - 1)` using `by ring`. Use `norm_sub_le (w + 1) (w - 1)` as an intermediate fact. Rewrite `this` using `[← e]`. Establish `n2 : ‖(2 : ℂ)‖ = 2` using `by simp`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `eq : z ^ (2 ^ (k + 1)) - 1 = (w - 1) * (w + 1)`. Rewrite using `[hw, pow_succ, pow_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eq, norm_mul, pow_succ]`.

Establish `h0 : 0 ≤ ‖z - 1‖` using `norm_nonneg _`. Establish `h0' : 0 ≤ (3 / 2 : ℝ) ^ k` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_pow_two_pow_sub_one_ge {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < (1 / 2 : ℝ)) :
    ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    set w := z ^ (2 ^ k) with hw
    have hw1 : ‖w - 1‖ < 1 / 2 := h _
    have h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
      have e : (2 : ℂ) = (w + 1) - (w - 1) := by ring
      have := norm_sub_le (w + 1) (w - 1)
      rw [← e] at this
      have n2 : ‖(2 : ℂ)‖ = 2 := by simp
      linarith
    have eq : z ^ (2 ^ (k + 1)) - 1 = (w - 1) * (w + 1) := by
      rw [hw, pow_succ, pow_mul]; ring
    rw [eq, norm_mul, pow_succ]
    have h0 : 0 ≤ ‖z - 1‖ := norm_nonneg _
    have h0' : 0 ≤ (3 / 2 : ℝ) ^ k := by positivity
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖w - 1‖ * ‖w + 1‖ := mul_le_mul ih h2 (by norm_num) (norm_nonneg _)

/- English proof (translation)
Introduce `z h`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖z - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hne)`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)`. Establish `h1 : (1 / 2 : ℝ) < (3 / 2 : ℝ) ^ k * ‖z - 1‖` using `(div_lt_iff₀ hpos).mp hk`.

Establish `h2` using `norm_pow_two_pow_sub_one_ge h k`. Establish `h3` using `h (2 ^ k)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 : (1 / 2 : ℝ) < (3 / 2 : ℝ) ^ k * ‖z - 1‖ := (div_lt_iff₀ hpos).mp hk
  have h2 := norm_pow_two_pow_sub_one_ge h k
  have h3 := h (2 ^ k)
  linarith

end GlobalTheory.PowerTwoNormLowerBound
