import Mathlib

/- English proof (translation)
Introduce `d hd z hz`. Establish `hre : z.re * z.re - z.im * z.im = -(d : ℝ)`. Establish `h` using `congrArg Complex.re hz`. Simplify `h` using `[pow_two]`. Establish `him : z.re * z.im + z.im * z.re = 0`.

Establish `h` using `congrArg Complex.im hz`. Simplify `h` using `[pow_two]`. Establish `hd' : (0 : ℝ) < d` using `by exact_mod_cast hd`. Establish `h0 : z.re = 0`. Establish `hmul : z.re * z.im = 0` using `by linarith [mul_comm z.im z.re]`.

Break down `mul_eq_zero.mp hmul with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Rewrite `hre` using `[h]`. Use polynomial arithmetic with `[mul_self_nonneg z.re]`.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[h0]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Reformulated.B.ConjEqNegOfSquare.conj_eq_neg_of_sq :
    ∀ {d : ℕ},
    (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d hd z hz
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have h := congrArg Complex.re hz
    simpa [pow_two] using h
  have him : z.re * z.im + z.im * z.re = 0 := by
    have h := congrArg Complex.im hz
    simpa [pow_two] using h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h0 : z.re = 0 := by
    have hmul : z.re * z.im = 0 := by linarith [mul_comm z.im z.re]
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exfalso
      rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp
