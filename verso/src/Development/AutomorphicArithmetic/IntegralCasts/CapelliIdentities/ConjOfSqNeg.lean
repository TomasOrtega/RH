import Mathlib

/- English proof (translation)
Introduce `t r hr h`. Establish `h1 : t.re * t.re - t.im * t.im = r`. Use `congrArg Complex.re h` as an intermediate fact. Simplify `this` using `[pow_two]`. Establish `h2 : t.re * t.im + t.im * t.re = 0`.

Use `congrArg Complex.im h` as an intermediate fact. Simplify `this` using `[pow_two]`. Establish `h3 : t.re = 0`. Establish `hm : t.re * t.im = 0` using `by linarith [mul_comm t.im t.re]`. Break down `mul_eq_zero.mp hm with h0 | h0` into its components or cases.

Conclude with `h0`. It suffices to derive a contradiction. Rewrite `h1` using `[h0]`. Use polynomial arithmetic with `[mul_self_nonneg t.re]`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using `[h3]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Reformulated.B.Qh17.conj_of_sq_neg :
    ∀ {t : ℂ} {r : ℝ},
    r < (0 : ℝ) → t ^ (2 : ℕ) = (↑r : ℂ) → (starRingEnd ℂ : ℂ → ℂ) t = -t := by
  intro t r hr h
  have h1 : t.re * t.re - t.im * t.im = r := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have h2 : t.re * t.im + t.im * t.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have h3 : t.re = 0 := by
    have hm : t.re * t.im = 0 := by linarith [mul_comm t.im t.re]
    rcases mul_eq_zero.mp hm with h0 | h0
    · exact h0
    · exfalso
      rw [h0] at h1
      nlinarith [mul_self_nonneg t.re]
  apply Complex.ext
  · simp [h3]
  · simp
