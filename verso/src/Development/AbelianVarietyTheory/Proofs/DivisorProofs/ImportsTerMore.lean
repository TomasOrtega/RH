import Mathlib

namespace GlobalTheory.InductiveNormBound

/- English proof (translation)
Establish `e : w^2 - 1 = (w - 1) * ((w - 1) + 2)` using `by ring`. Rewrite using `[e, norm_mul]`. Establish `h2 : (3/2 : ℝ) ≤ ‖(w - 1) + 2‖`. Establish `h3` using `norm_sub_le ((w - 1) + 2) (w - 1)`. Establish `h4 : (w - 1) + 2 - (w - 1) = (2:ℂ)` using `by ring`.

Rewrite `h3` using `[h4]`. Establish `: ‖(2:ℂ)‖ = 2` using `by simp`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0` using `norm_nonneg (w - 1)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w^2 - 1‖ := by
  have e : w^2 - 1 = (w - 1) * ((w - 1) + 2) := by ring
  rw [e, norm_mul]
  have h2 : (3/2 : ℝ) ≤ ‖(w - 1) + 2‖ := by
    have h3 := norm_sub_le ((w - 1) + 2) (w - 1)
    have h4 : (w - 1) + 2 - (w - 1) = (2:ℂ) := by ring
    rw [h4] at h3
    have : ‖(2:ℂ)‖ = 2 := by simp
    linarith
  have h0 := norm_nonneg (w - 1)
  nlinarith

/- English proof (translation)
Introduce `z hz`. Establish `key : ∀ k : ℕ, (3/2 : ℝ)^k * ‖z - 1‖ ≤ ‖z^(2^k) - 1‖`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Establish `hs` using `step (z^(2^k)) (hz _)`. Establish `e : (z^(2^k))^2 = z^(2^(k+1))` using `by rw [← pow_mul, ← pow_succ]`. Rewrite `hs` using `[e]`. Establish `hp : (3/2:ℝ)^(k+1) = (3/2)^k * (3/2)` using `pow_succ _ _`.

Rewrite using `[hp]`. Use polynomial arithmetic with `[ih, hs]`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖z - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hne)`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (1 / ‖z - 1‖) (by norm_num : (1:ℝ) < 3/2)`.

Establish `h1` using `key k`. Establish `h2` using `hz (2^k)`. Establish `h3 : 1 < (3/2:ℝ)^k * ‖z - 1‖`. Rewrite `hk` using `[div_lt_iff₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  have key : ∀ k : ℕ, (3/2 : ℝ)^k * ‖z - 1‖ ≤ ‖z^(2^k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := step (z^(2^k)) (hz _)
      have e : (z^(2^k))^2 = z^(2^(k+1)) := by rw [← pow_mul, ← pow_succ]
      rw [e] at hs
      have hp : (3/2:ℝ)^(k+1) = (3/2)^k * (3/2) := pow_succ _ _
      rw [hp]
      nlinarith [ih, hs]
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ‖z - 1‖) (by norm_num : (1:ℝ) < 3/2)
  have h1 := key k
  have h2 := hz (2^k)
  have h3 : 1 < (3/2:ℝ)^k * ‖z - 1‖ := by
    rw [div_lt_iff₀ hpos] at hk; linarith
  linarith

/- English proof (translation)
The claim follows from `main`.
-/
example : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := main

end GlobalTheory.InductiveNormBound
