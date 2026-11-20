import Formalism.EisensteinCokernelLengths.ExponentChainBound
import Formalism.EisensteinCokernelLengths.RationalTailBound

noncomputable section

namespace Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exponentChainBound : ExponentChainBound := by
  unfold ExponentChainBound
  intro ℓ b b' S E lam σ₂ h'' c' hℓ hb hS hE hσ hlam hc
  have h1 : 0 < ℓ - 1 := by linarith
  have h0 : 0 < ℓ := by linarith
  have h1' : ℓ - 1 ≠ 0 := h1.ne'
  have h0' : ℓ ≠ 0 := h0.ne'
  have key : b / (ℓ - 1) - b / ℓ = b / (ℓ * (ℓ - 1)) := by
    field_simp; ring
  have hS1 : (S + 1) / (ℓ - 1) ≤ S + 1 := div_le_self (by linarith) (by linarith)
  have hsplit : ((b + S) + 1) / (ℓ - 1) = b / (ℓ - 1) + (S + 1) / (ℓ - 1) := by ring
  have hnn : 0 ≤ b / (ℓ * (ℓ - 1)) := div_nonneg hb (mul_pos h0 h1).le
  apply max_le
  · linarith
  · linarith

/- English proof (translation)
Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma numC_cubic (ℓ : ℝ) (hℓ : 11 ≤ ℓ) :
    8 * (2 * ℓ - 1) * ℓ ^ 2 + 8 * ℓ ^ 2 * (ℓ - 1) + ℓ * (ℓ - 1) ^ 2 ≤ 3111 / 100 * (ℓ - 1) ^ 3 := by
  have ht : 0 ≤ ℓ - 11 := by linarith
  nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem rationalTailBoundCubic : NumC := by
  unfold NumC
  intro ℓ hℓ
  have h1 : 0 < ℓ - 1 := by linarith
  have h0 : 0 < ℓ := by linarith
  have h1' : ℓ - 1 ≠ 0 := h1.ne'
  have h0' : ℓ ≠ 0 := h0.ne'
  have key := numC_cubic ℓ hℓ
  have e : 8 * (2 * ℓ - 1) / (ℓ - 1) ^ 3 + 8 / (ℓ - 1) ^ 2 + 1 / (ℓ * (ℓ - 1)) =
      (8 * (2 * ℓ - 1) * ℓ ^ 2 + 8 * ℓ ^ 2 * (ℓ - 1) + ℓ * (ℓ - 1) ^ 2) / (ℓ ^ 2 * (ℓ - 1) ^ 3) := by
    field_simp
  have c : (31.11 : ℝ) = 3111 / 100 := by norm_num
  rw [e, div_le_div_iff₀ (mul_pos (pow_pos h0 2) (pow_pos h1 3)) (pow_pos h0 2), c]
  nlinarith [mul_le_mul_of_nonneg_right key (sq_nonneg ℓ)]

end Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
