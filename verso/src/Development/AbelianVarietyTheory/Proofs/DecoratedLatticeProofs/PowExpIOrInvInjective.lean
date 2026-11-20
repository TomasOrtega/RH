import Mathlib

namespace GlobalTheory.ExpPow

/- English proof (translation)
Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.mp h`. Establish `h1 : (m : ℝ) = n * (2 * Real.pi)`. Use `congrArg Complex.im hn` as an intermediate fact. Simplify using `using this`. Assume the negation of the conclusion as `hm`.

Establish `hn0 : (n : ℝ) ≠ 0`. Introduce `h0`. Rewrite `h1` using `[h0, zero_mul]`. Conclude with `hm (by exact_mod_cast h1)`. Apply `irrational_pi` to reduce the goal to its premises.

Use `⟨(m : ℚ) / (2 * n), ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem int_eq_zero_of_exp_I_mul (m : ℤ) (h : Complex.exp (Complex.I * m) = 1) : m = 0 := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h1 : (m : ℝ) = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  by_contra hm
  have hn0 : (n : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact hm (by exact_mod_cast h1)
  apply irrational_pi
  refine ⟨(m : ℚ) / (2 * n), ?_⟩
  push_cast
  rw [h1]
  field_simp

/- English proof (translation)
Rewrite `h` using `[← Complex.exp_nat_mul, ← Complex.exp_nat_mul]`. Establish `h2 : Complex.exp (Complex.I * (((a : ℤ) - b : ℤ) : ℂ)) = 1`. Establish `: Complex.I * (((a : ℤ) - b : ℤ) : ℂ) = a * Complex.I - b * Complex.I` using `by push_cast; ring`. Rewrite using `[this, Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]`. Use `int_eq_zero_of_exp_I_mul _ h2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem exp_I_pow_injective (a b : ℕ)
    (h : Complex.exp Complex.I ^ a = Complex.exp Complex.I ^ b) : a = b := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul] at h
  have h2 : Complex.exp (Complex.I * (((a : ℤ) - b : ℤ) : ℂ)) = 1 := by
    have : Complex.I * (((a : ℤ) - b : ℤ) : ℂ) = a * Complex.I - b * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
  have := int_eq_zero_of_exp_I_mul _ h2
  omega

/- English proof (translation)
Introduce and unpack `a b w (rfl | rfl) h`. Conclude with `exp_I_pow_injective a b h`. Rewrite `h` using `[inv_pow, inv_pow, inv_inj]`. Conclude with `exp_I_pow_injective a b h`.
-/
theorem pow_exp_I_or_inv_injective :
    ∀ (a b : ℕ) (w : ℂ), (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) →
      w ^ a = w ^ b → a = b := by
  rintro a b w (rfl | rfl) h
  · exact exp_I_pow_injective a b h
  · rw [inv_pow, inv_pow, inv_inj] at h
    exact exp_I_pow_injective a b h

end GlobalTheory.ExpPow
