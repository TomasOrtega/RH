import Mathlib

namespace GlobalTheory.CMModel

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem cubic_three_roots (g h e₁ e₂ e₃ : ℂ) (h₁ : 4 * e₁ ^ 3 - g * e₁ - h = 0)
    (h₂ : 4 * e₂ ^ 3 - g * e₂ - h = 0) (h₃ : 4 * e₃ ^ 3 - g * e₃ - h = 0)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    (∀ x, 4 * x ^ 3 - g * x - h = 4 * (x - e₁) * (x - e₂) * (x - e₃)) ∧
      16 * ((3 * e₁ ^ 2 - g / 4) * (3 * e₂ ^ 2 - g / 4) * (3 * e₃ ^ 2 - g / 4))
        = -(g ^ 3 - 27 * h ^ 2) := by
  have a : g = 4 * (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₂)
    linear_combination h₂ - h₁
  have b : g = 4 * (e₁ ^ 2 + e₁ * e₃ + e₃ ^ 2) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₃)
    linear_combination h₃ - h₁
  have c : e₃ = -e₁ - e₂ := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₂₃)
    linear_combination (b - a) / 4
  have d : h = 4 * e₁ ^ 3 - g * e₁ := by linear_combination -h₁
  subst c
  rw [d, a]
  exact ⟨fun x => by ring, by ring⟩

end GlobalTheory.CMModel
