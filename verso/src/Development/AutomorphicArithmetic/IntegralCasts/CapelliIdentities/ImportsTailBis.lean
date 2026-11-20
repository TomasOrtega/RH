import Mathlib

/- English proof (translation)
Introduce `j`. Use `split_ifs with hj`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Establish `hc : (2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑j : ℂ) ≠ 0`.

Establish `: (j : ℂ) ≠ 0` using `by exact_mod_cast hj`. Establish `hpi : (↑Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Simplify using `[hpi, this, Complex.I_ne_zero]`. Rewrite using `[integral_exp_mul_complex hc]`. Establish `h1 : Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑j : ℂ) * ((1:ℝ) : ℂ)) = 1`.

Rewrite using `[Complex.exp_eq_one_iff]`. Conclude with `⟨j, by push_cast; ring⟩`. Rewrite using `[h1]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Reformulated.B.Yra2.main :
    ∀ (j : ℤ),
      ∫ (x : ℝ) in (0 : ℝ)..(1 : ℝ), Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑j : ℂ) * (↑x : ℂ)) =
        if j = (0 : ℤ) then (1 : ℂ) else (0 : ℂ) := by
  intro j
  split_ifs with hj
  · subst hj
    simp
  · have hc : (2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑j : ℂ) ≠ 0 := by
      have : (j : ℂ) ≠ 0 := by exact_mod_cast hj
      have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, this, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑j : ℂ) * ((1:ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨j, by push_cast; ring⟩
    rw [h1]
    simp
