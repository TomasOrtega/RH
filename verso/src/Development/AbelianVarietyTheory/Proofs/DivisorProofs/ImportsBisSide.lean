import Mathlib

namespace GlobalTheory.PositiveFormRecursion

/- English proof (translation)
Establish `h1 : w ^ 2 - 1 = (w - 1) * (w + 1)` using `by ring`. Establish `h2 : (3/2 : ℝ) ≤ ‖w + 1‖`. Establish `e : (2 : ℂ) = (w + 1) - (w - 1)` using `by ring`. Establish `h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖`. Rewrite using `[e]`.

Conclude with `norm_sub_le _ _`. Establish `h4 : ‖(2 : ℂ)‖ = 2` using `by norm_num`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h1, norm_mul]`. Use polynomial arithmetic with `[norm_nonneg (w - 1)]`.
-/
theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have h1 : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (3/2 : ℝ) ≤ ‖w + 1‖ := by
    have e : (2 : ℂ) = (w + 1) - (w - 1) := by ring
    have h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
      rw [e]; exact norm_sub_le _ _
    have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
    linarith
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (w - 1)]

/- English proof (translation)
Introduce `z hz`. Establish `key : ∀ n : ℕ, (3/2 : ℝ) ^ n * ‖z - 1‖ ≤ ‖z ^ (2 : ℕ) ^ n - 1‖`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Establish `e : z ^ (2 : ℕ) ^ (n + 1) = (z ^ (2 : ℕ) ^ n) ^ 2` using `by rw [pow_succ, pow_mul]`. Rewrite using `[e]`. Establish `hs` using `step (z ^ (2 : ℕ) ^ n) (hz n)`. Combine the equalities or inequalities in the displayed calculation.

Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖z - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hne)`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3/2)`. Establish `hn'` using `(div_lt_iff₀ (by positivity)).mp hn`. Establish `h1` using `key n`.

Establish `h2` using `hz n`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ (2 : ℕ) ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  have key : ∀ n : ℕ, (3/2 : ℝ) ^ n * ‖z - 1‖ ≤ ‖z ^ (2 : ℕ) ^ n - 1‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : z ^ (2 : ℕ) ^ (n + 1) = (z ^ (2 : ℕ) ^ n) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e]
      have hs := step (z ^ (2 : ℕ) ^ n) (hz n)
      calc (3/2 : ℝ) ^ (n + 1) * ‖z - 1‖ = (3/2) * ((3/2) ^ n * ‖z - 1‖) := by ring
        _ ≤ (3/2) * ‖z ^ (2 : ℕ) ^ n - 1‖ := by gcongr
        _ ≤ _ := hs
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3/2)
  have hn' := (div_lt_iff₀ (by positivity)).mp hn
  have h1 := key n
  have h2 := hz n
  nlinarith

end GlobalTheory.PositiveFormRecursion
