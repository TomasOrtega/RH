import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer

namespace GlobalTheory

/- English proof (translation)
Use `⟨3 + 2 ^ d * (d.factorial : ℝ), fun s hs hs1 => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `hpos : (0 : ℝ) ≤ 2 ^ d * (d.factorial : ℝ)` using `by positivity`. Establish `hx : (0 : ℝ) < (s ^ 2)⁻¹ / 3` using `by positivity`. Establish `h1 : (s ^ 2)⁻¹ / 3 ≤ Real.exp ((s ^ 2)⁻¹ / 3)`. Use `Real.add_one_le_exp ((s ^ 2)⁻¹ / 3)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : Real.exp (-(s ^ 2)⁻¹ / 3) ≤ 3 * s ^ 2`. Rewrite using `[neg_div, Real.exp_neg]`. Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[mul_nonneg hpos hs.le, mul_nonneg hs.le (sub_nonneg.2 hs1)]`.

Establish `hl : 0 ≤ Real.log s⁻¹` using `Real.log_nonneg ((one_le_inv₀ hs).2 hs1)`. Establish `h1 : Real.log s⁻¹ ^ d / (d.factorial : ℝ) ≤ s⁻¹`. Use `Real.pow_div_factorial_le_exp (Real.log s⁻¹) hl d` as an intermediate fact. Rewrite `this` using `[Real.exp_log (inv_pos.2 hs)]`. Then use the resulting hypothesis. Establish `hf : (0 : ℝ) < (d.factorial : ℝ)` using `by exact_mod_cast d.factorial_pos`.

Establish `h2 : Real.log s⁻¹ ^ d ≤ s⁻¹ * (d.factorial : ℝ)` using `(div_le_iff₀ hf).1 h1`. Establish `h3 : Real.log ((s ^ 2)⁻¹) = 2 * Real.log s⁻¹`. Rewrite using `[← inv_pow, Real.log_pow]`. Evaluate the numerical expressions. Rewrite using `[h3, mul_pow, div_inv_eq_mul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exp_neg_and_log_pow_div_le_mul (d : ℕ) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 →
      Real.exp (-(s ^ 2)⁻¹ / 3) ≤ C * s ∧ Real.log ((s ^ 2)⁻¹) ^ d / (s ^ 2)⁻¹ ≤ C * s := by
  refine ⟨3 + 2 ^ d * (d.factorial : ℝ), fun s hs hs1 => ⟨?_, ?_⟩⟩
  · have hpos : (0 : ℝ) ≤ 2 ^ d * (d.factorial : ℝ) := by positivity
    have hx : (0 : ℝ) < (s ^ 2)⁻¹ / 3 := by positivity
    have h1 : (s ^ 2)⁻¹ / 3 ≤ Real.exp ((s ^ 2)⁻¹ / 3) := by
      have := Real.add_one_le_exp ((s ^ 2)⁻¹ / 3)
      linarith
    have h2 : Real.exp (-(s ^ 2)⁻¹ / 3) ≤ 3 * s ^ 2 := by
      rw [neg_div, Real.exp_neg]
      calc (Real.exp ((s ^ 2)⁻¹ / 3))⁻¹ ≤ ((s ^ 2)⁻¹ / 3)⁻¹ := inv_anti₀ hx h1
        _ = 3 * s ^ 2 := by field_simp
    nlinarith [mul_nonneg hpos hs.le, mul_nonneg hs.le (sub_nonneg.2 hs1)]
  · have hl : 0 ≤ Real.log s⁻¹ := Real.log_nonneg ((one_le_inv₀ hs).2 hs1)
    have h1 : Real.log s⁻¹ ^ d / (d.factorial : ℝ) ≤ s⁻¹ := by
      have := Real.pow_div_factorial_le_exp (Real.log s⁻¹) hl d
      rwa [Real.exp_log (inv_pos.2 hs)] at this
    have hf : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast d.factorial_pos
    have h2 : Real.log s⁻¹ ^ d ≤ s⁻¹ * (d.factorial : ℝ) := (div_le_iff₀ hf).1 h1
    have h3 : Real.log ((s ^ 2)⁻¹) = 2 * Real.log s⁻¹ := by
      rw [← inv_pow, Real.log_pow]; norm_num
    rw [h3, mul_pow, div_inv_eq_mul]
    calc 2 ^ d * Real.log s⁻¹ ^ d * s ^ 2 ≤ 2 ^ d * (s⁻¹ * (d.factorial : ℝ)) * s ^ 2 := by
          gcongr
      _ = 2 ^ d * (d.factorial : ℝ) * s := by field_simp
      _ ≤ (3 + 2 ^ d * (d.factorial : ℝ)) * s := by nlinarith

end GlobalTheory
