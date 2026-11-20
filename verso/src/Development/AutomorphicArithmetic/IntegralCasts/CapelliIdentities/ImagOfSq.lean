import Mathlib

/- English proof (translation)
Introduce `c d hd h`. Establish `hd' : (0 : ℝ) < d` using `Nat.cast_pos.mpr hd`. Establish `h1 : c.re * c.re - c.im * c.im = -(d : ℝ)`. Use `congrArg Complex.re h` as an intermediate fact. Simplify `this` using `[pow_two]`.

Establish `h2 : c.re * c.im + c.im * c.re = 0`. Use `congrArg Complex.im h` as an intermediate fact. Simplify `this` using `[pow_two]`. Establish `h3 : c.re * c.im = 0` using `by linarith [mul_comm c.re c.im]`. Establish `hre : c.re = 0`.

Break down `mul_eq_zero.mp h3 with h4 | h4` into its components or cases. Conclude with `h4`. Rewrite `h1` using `[h4]`. Use polynomial arithmetic with `[mul_self_nonneg c.re]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[hre]`. Simplify using the standard rewrite rules. Introduce and unpack `rfl`. Simplify using `at h1`.

Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.Reformulated.B.Qh67.imag_of_sq :
    ∀ {c : ℂ} {d : ℕ},
    (0 : ℕ) < d → c ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) c = -c ∧ c ≠ (0 : ℂ) := by
  intro c d hd h
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h1 : c.re * c.re - c.im * c.im = -(d : ℝ) := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have h2 : c.re * c.im + c.im * c.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have h3 : c.re * c.im = 0 := by linarith [mul_comm c.re c.im]
  have hre : c.re = 0 := by
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · rw [h4] at h1
      nlinarith [mul_self_nonneg c.re]
  refine ⟨?_, ?_⟩
  · apply Complex.ext
    · simp [hre]
    · simp
  · rintro rfl
    simp at h1
    omega
