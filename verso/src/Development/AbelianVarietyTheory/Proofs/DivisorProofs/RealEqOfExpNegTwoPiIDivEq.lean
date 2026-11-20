import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨n, hn⟩` from `Complex.exp_eq_exp_iff_exists_int.mp h`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hk' : (k : ℂ) ≠ 0` using `by exact_mod_cast hk.ne'`. Establish `hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`.

Establish `: ((y - x : ℝ) : ℂ) = ((n * k : ℝ) : ℂ)`. Use `push_cast`. Clear denominators, using `at hn` for the nonvanishing conditions. Take the linear combination `hn`. Conclude with `this` after adjusting the coercions.
-/
theorem exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq (x y : ℝ) (k : ℕ) (hk : 0 < k)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) :
    ∃ n : ℤ, y - x = n * k := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : ((y - x : ℝ) : ℂ) = ((n * k : ℝ) : ℂ) := by
    push_cast
    field_simp at hn
    linear_combination hn
  exact_mod_cast this

/- English proof (translation)
Introduce `x y h`. Take `⟨m, hm⟩` from `exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq x y 1 one_pos (h 1 one_pos)`. Simplify using `only [Nat.cast_one, mul_one] at hm`. Take `⟨n, hn⟩` from `exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq x y (m.natAbs + 1) (Nat.succ_pos _) (h _ (Nat.succ_pos _))`. Generalize the expression as in `hK : m.natAbs + 1 = K at hn`.

Establish `hmn : m = n * (K : ℤ)`. Establish `: ((m : ℤ) : ℝ) = ((n * (K : ℤ) : ℤ) : ℝ)` using `by push_cast; rw [← hm, hn]`. Conclude with `this` after adjusting the coercions. Establish `hm0 : m = 0`. Assume the negation of the conclusion as `hne`.

Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `hne (by simpa using hmn)`. Establish `h1 : m.natAbs = n.natAbs * K`. Rewrite using `[hmn, Int.natAbs_mul]`.

Simplify using the standard rewrite rules. Establish `h2 : 1 ≤ n.natAbs` using `Int.natAbs_pos.mpr hn0`. Use the polynomial consequences of the given equalities and inequalities. Establish `: y - x = 0` using `by rw [hm, hm0]; simp`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem real_eq_of_exp_neg_two_pi_I_div_eq : ∀ x y : ℝ, (∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) →
    x = y := by
  intro x y h
  obtain ⟨m, hm⟩ := exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq x y 1 one_pos (h 1 one_pos)
  simp only [Nat.cast_one, mul_one] at hm
  obtain ⟨n, hn⟩ := exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq x y (m.natAbs + 1) (Nat.succ_pos _)
    (h _ (Nat.succ_pos _))
  generalize hK : m.natAbs + 1 = K at hn
  have hmn : m = n * (K : ℤ) := by
    have : ((m : ℤ) : ℝ) = ((n * (K : ℤ) : ℤ) : ℝ) := by push_cast; rw [← hm, hn]
    exact_mod_cast this
  have hm0 : m = 0 := by
    by_contra hne
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hmn)
    have h1 : m.natAbs = n.natAbs * K := by
      rw [hmn, Int.natAbs_mul]; simp
    have h2 : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn0
    nlinarith
  have : y - x = 0 := by rw [hm, hm0]; simp
  linarith

end GlobalTheory
