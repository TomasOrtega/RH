import Mathlib

namespace GlobalTheory.PowerScaledNormBound

/- English proof (translation)
Establish `hprime : p.Prime` using `Fact.out`. Establish `hp : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹`. Rewrite using `[← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p p]`. Simplify using the standard rewrite rules. Establish `hp1 : (p : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast hprime.one_lt)`.

Establish `hy` using `norm_nonneg y`. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖y‖ + 1) by positivity) hp1`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow, hp]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_pow_mul_norm_le_one (p : ℕ) [Fact (Nat.Prime p)] (y : PadicAlgCl p) :
    ∃ k : ℕ, ‖(p : PadicAlgCl p) ^ k * y‖ ≤ (1 : ℝ) := by
  have hprime : p.Prime := Fact.out
  have hp : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
    rw [← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p p]
    simp
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hprime.one_lt)
  have hy := norm_nonneg y
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖y‖ + 1) by positivity) hp1
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_pow, hp]
  calc (p : ℝ)⁻¹ ^ k * ‖y‖ ≤ 1 / (‖y‖ + 1) * ‖y‖ := mul_le_mul_of_nonneg_right hk.le hy
    _ ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith

end GlobalTheory.PowerScaledNormBound
