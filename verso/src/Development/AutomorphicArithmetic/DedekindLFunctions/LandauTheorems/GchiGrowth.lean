import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Establish `hy0 : 0 ≤ y` using `by linarith`. Establish `key : ∀ n ∈ Finset.range (⌊y⌋₊ + 1), ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)‖ ≤ y`. Introduce `n _`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `using hy0`.

Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `h1 : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ)` using `ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn'.le)`. Establish `h0 : 0 ≤ ArithmeticFunction.vonMangoldt n` using `ArithmeticFunction.vonMangoldt_nonneg`. Establish `h2 : max (y / n - 1) 0 ≤ y / n` using `max_le (by linarith) (by positivity)`. Establish `h3 : 0 ≤ max (y / n - 1) 0` using `le_max_right _ _`.

Rewrite using `[norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h0, Real.norm_of_nonneg h3]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hf n`. Use `_ = y := by field_simp`. Establish `h` using `(norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ key)`.

Rewrite `h` using `[Finset.card_range, nsmul_eq_mul]`. Establish `hfl : (⌊y⌋₊ : ℝ) ≤ y` using `Nat.floor_le hy0`. Unfold `ramp`. Use `h.trans ?_` and prove the remaining obligations. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem Gchi_growth_ramp (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {y : ℝ} (hy : 1 ≤ y) :
    ‖ramp f y‖ ≤ 2 * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have key : ∀ n ∈ Finset.range (⌊y⌋₊ + 1),
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)‖ ≤ y := by
    intro n _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hy0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn'.le)
    have h0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have h2 : max (y / n - 1) 0 ≤ y / n := max_le (by linarith) (by positivity)
    have h3 : 0 ≤ max (y / n - 1) 0 := le_max_right _ _
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h0,
      Real.norm_of_nonneg h3]
    calc _ ≤ (n : ℝ) * 1 * (y / n) := by
          gcongr
          exact hf n
      _ = y := by field_simp
  have h := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ key)
  rw [Finset.card_range, nsmul_eq_mul] at h
  have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  unfold ramp
  refine h.trans ?_
  push_cast
  nlinarith

/- English proof (translation)
Distinguish the cases in `h : χ = 1`. Use `⟨2 + 1 + |1 + Real.eulerMascheroniConstant|, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hr` using `Gchi_growth_ramp (fun n => χ n) (fun n => χ.norm_le_one _) hy`. Establish `hy0 : 0 ≤ y` using `by linarith`. Establish `hl0 : 0 ≤ Real.log y` using `Real.log_nonneg hy`.

Establish `hl : Real.log y ≤ y` using `Real.log_le_self hy0`. Establish `hyy : y ≤ y ^ 2` using `by nlinarith`. Unfold `Gchi`. Rewrite using `[if_pos h]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations.

Use `(add_le_add (norm_sub_le _ _) le_rfl).trans ?_` and prove the remaining obligations. Rewrite using `[Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hy0 hl0), Real.norm_eq_abs, abs_mul, abs_of_nonneg hy0]`. Establish `h1 : y * Real.log y ≤ y ^ 2` using `by nlinarith`. Establish `h2` using `mul_le_mul_of_nonneg_left hyy (abs_nonneg (1 + Real.eulerMascheroniConstant))`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨2 + ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hr` using `Gchi_growth_ramp (fun n => χ n) (fun n => χ.norm_le_one _) hy`. Establish `hy0 : 0 ≤ y` using `by linarith`. Establish `hyy : y ≤ y ^ 2` using `by nlinarith`. Unfold `Gchi`.

Rewrite using `[if_neg h]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0]`. Establish `h2` using `mul_le_mul_of_nonneg_left hyy (norm_nonneg (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Gchi_growth {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → ‖Gchi χ y‖ ≤ C * y ^ 2 := by
  by_cases h : χ = 1
  · refine ⟨2 + 1 + |1 + Real.eulerMascheroniConstant|, fun y hy => ?_⟩
    have hr := Gchi_growth_ramp (fun n => χ n) (fun n => χ.norm_le_one _) hy
    have hy0 : 0 ≤ y := by linarith
    have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy
    have hl : Real.log y ≤ y := Real.log_le_self hy0
    have hyy : y ≤ y ^ 2 := by nlinarith
    unfold Gchi
    rw [if_pos h]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
    rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hy0 hl0),
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hy0]
    have h1 : y * Real.log y ≤ y ^ 2 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left hyy (abs_nonneg (1 + Real.eulerMascheroniConstant))
    linarith
  · refine ⟨2 + ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖,
      fun y hy => ?_⟩
    have hr := Gchi_growth_ramp (fun n => χ n) (fun n => χ.norm_le_one _) hy
    have hy0 : 0 ≤ y := by linarith
    have hyy : y ≤ y ^ 2 := by nlinarith
    unfold Gchi
    rw [if_neg h]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0]
    have h2 := mul_le_mul_of_nonneg_left hyy
      (norm_nonneg (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1))
    linarith

end Deduction

end
