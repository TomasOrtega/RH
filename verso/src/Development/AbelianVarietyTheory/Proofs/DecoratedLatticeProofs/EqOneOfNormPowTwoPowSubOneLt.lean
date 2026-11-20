import Mathlib

namespace GlobalTheory.NormPowerTwoUnity

/- English proof (translation)
Establish `e : w ^ 2 - 1 = (w + 1) * (w - 1)` using `by ring`. Establish `h2 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖`. Establish `: (2 : ℂ) = (w + 1) - (w - 1)` using `by ring`. Rewrite using `[this]`. Conclude with `norm_sub_le _ _`.

Establish `h3 : ‖(2 : ℂ)‖ = 2` using `by simp`. Rewrite using `[e, norm_mul]`. Apply `mul_le_mul_of_nonneg_right _ (norm_nonneg _)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma norm_sq_sub_one_ge (w : ℂ) (h : ‖w - 1‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w + 1) * (w - 1) := by ring
  have h2 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have : (2 : ℂ) = (w + 1) - (w - 1) := by ring
    rw [this]
    exact norm_sub_le _ _
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  linarith

/- English proof (translation)
Establish `key : ∀ m : ℕ, (3 / 2 : ℝ) ^ m * ‖z - 1‖ ≤ ‖z ^ (2 : ℕ) ^ m - (1 : ℂ)‖`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Establish `h1` using `norm_sq_sub_one_ge _ (h n)`. Rewrite `h1` using `[← pow_mul, ← pow_succ]`. Combine the equalities or inequalities in the displayed calculation. Assume the negation of the conclusion as `hz`. Establish `hpos : 0 < ‖z - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hz)`.

Take `⟨m, hm⟩` from `pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (show (1 : ℝ) < 3 / 2 by norm_num)`. Rewrite `hm` using `[div_lt_iff₀ hpos]`. Use `key m` as an intermediate fact. Use `h m` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_one_of_norm_pow_two_pow_sub_one_lt (z : ℂ)
    (h : ∀ (m : ℕ), ‖z ^ (2 : ℕ) ^ m - (1 : ℂ)‖ < (1 / 2 : ℝ)) : z = (1 : ℂ) := by
  have key : ∀ m : ℕ, (3 / 2 : ℝ) ^ m * ‖z - 1‖ ≤ ‖z ^ (2 : ℕ) ^ m - (1 : ℂ)‖ := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      have h1 := norm_sq_sub_one_ge _ (h n)
      rw [← pow_mul, ← pow_succ] at h1
      calc (3 / 2 : ℝ) ^ (n + 1) * ‖z - 1‖ = (3 / 2) * ((3 / 2 : ℝ) ^ n * ‖z - 1‖) := by ring
        _ ≤ (3 / 2) * ‖z ^ (2 : ℕ) ^ n - (1 : ℂ)‖ := by linarith
        _ ≤ _ := h1
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (show (1 : ℝ) < 3 / 2 by norm_num)
  rw [div_lt_iff₀ hpos] at hm
  have := key m
  have := h m
  linarith

end GlobalTheory.NormPowerTwoUnity
