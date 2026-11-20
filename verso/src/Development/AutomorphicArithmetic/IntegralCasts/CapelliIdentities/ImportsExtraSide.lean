import Mathlib

/- English proof (translation)
Introduce `d hd z hz`. Establish `h1 : (z ^ 2).re = z.re * z.re - z.im * z.im`. Rewrite using `[pow_two, Complex.mul_re]`. Establish `h2 : (z ^ 2).im = z.re * z.im + z.im * z.re`. Rewrite using `[pow_two, Complex.mul_im]`.

Establish `e1 : (-(d : ℂ)).re = -(d : ℝ)` using `by simp`. Establish `e2 : (-(d : ℂ)).im = 0` using `by simp`. Rewrite `h1` using `[hz, e1]`. Rewrite `h2` using `[hz, e2]`. Establish `hdpos : (0 : ℝ) < (d : ℝ)` using `by exact_mod_cast hd`.

Establish `hm : z.re * z.im = 0` using `by linarith`. Establish `ha : z.re = 0`. Break down `mul_eq_zero.mp hm with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Establish `: z.im * z.im = 0` using `by rw [h]; ring`. Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[ha]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Reformulated.B.Ydc3.main :
    ∀ {d : ℕ}, (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d hd z hz
  have h1 : (z ^ 2).re = z.re * z.re - z.im * z.im := by
    rw [pow_two, Complex.mul_re]
  have h2 : (z ^ 2).im = z.re * z.im + z.im * z.re := by
    rw [pow_two, Complex.mul_im]
  have e1 : (-(d : ℂ)).re = -(d : ℝ) := by simp
  have e2 : (-(d : ℂ)).im = 0 := by simp
  rw [hz, e1] at h1
  rw [hz, e2] at h2
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hm : z.re * z.im = 0 := by linarith
  have ha : z.re = 0 := by
    rcases mul_eq_zero.mp hm with h | h
    · exact h
    · exfalso
      have : z.im * z.im = 0 := by rw [h]; ring
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [ha]
  · simp
