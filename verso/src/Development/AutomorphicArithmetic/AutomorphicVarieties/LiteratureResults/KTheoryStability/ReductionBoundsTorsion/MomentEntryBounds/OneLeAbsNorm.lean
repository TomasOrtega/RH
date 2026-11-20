import Mathlib

open NumberField

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type*} [Field L] [NumberField L]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem exists_den (s : Finset L) : ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ s, IsIntegral ℤ ((d : L) * x) := by
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨d, hd, fun x hx => ?_⟩
  have := h x hx
  rwa [zsmul_eq_mul] at this

end PositivityTheory.KB.MomentRationality.Ht
