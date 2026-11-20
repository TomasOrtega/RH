import Mathlib

namespace GlobalTheory.CMModel

/- English proof (translation)
Establish `a : g = 4 * (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2)`. Apply `mul_left_cancel₀ (sub_ne_zero.mpr h₁₂)` to reduce the goal to its premises. Take the linear combination `h₂ - h₁`. Establish `b : g = 4 * (e₁ ^ 2 + e₁ * e₃ + e₃ ^ 2)`. Apply `mul_left_cancel₀ (sub_ne_zero.mpr h₁₃)` to reduce the goal to its premises.

Take the linear combination `h₃ - h₁`. Establish `c : e₃ = -e₁ - e₂`. Apply `mul_left_cancel₀ (sub_ne_zero.mpr h₂₃)` to reduce the goal to its premises. Take the linear combination `(b - a) / 4`. Establish `d : h = 4 * e₁ ^ 3 - g * e₁` using `by linear_combination -h₁`.

Substitute `c` using the available equality. Rewrite using `[d, a]`. Conclude with `⟨fun x => by ring, by ring⟩`.
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
