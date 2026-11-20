import Mathlib

/- English proof (translation)
Introduce `d hd z hz`. Establish `hd' : (0 : ℝ) < (d : ℝ)` using `by exact_mod_cast hd`. Establish `hre : z.re * z.re - z.im * z.im = -(d : ℝ)`. Establish `h` using `congrArg Complex.re hz`. Simplify `h` using `[pow_two]`.

Establish `him : z.re * z.im + z.im * z.re = 0`. Establish `h` using `congrArg Complex.im hz`. Simplify `h` using `[pow_two]`. Establish `hprod : z.re * z.im = 0` using `by linarith`. Establish `hre0 : z.re = 0`.

Break down `mul_eq_zero.mp hprod with h | h` into its components or cases. Conclude with `h`. Rewrite `hre` using `[h]`. Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using `[hre0]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Reformulated.B.ConjEqNegOfSqEqNegNat₂.main :
    ∀ {d : ℕ}, (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d hd z hz
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have h := congrArg Complex.re hz
    simpa [pow_two] using h
  have him : z.re * z.im + z.im * z.re = 0 := by
    have h := congrArg Complex.im hz
    simpa [pow_two] using h
  have hprod : z.re * z.im = 0 := by linarith
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [hre0]
  · simp
