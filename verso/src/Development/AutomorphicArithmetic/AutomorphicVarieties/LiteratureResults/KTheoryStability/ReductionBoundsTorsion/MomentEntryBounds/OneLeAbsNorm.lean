import Mathlib

open NumberField

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type*} [Field L] [NumberField L]

/- English proof (translation)
Take `⟨d, hd, h⟩` from `exists_integral_multiples ℤ ℚ s`. Use `⟨d, hd, fun x hx => ?_⟩` and prove the remaining obligations. Use `h x hx` as an intermediate fact. Rewrite `this` using `[zsmul_eq_mul]`. Then use the resulting hypothesis.
-/
theorem exists_den (s : Finset L) : ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ s, IsIntegral ℤ ((d : L) * x) := by
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨d, hd, fun x hx => ?_⟩
  have := h x hx
  rwa [zsmul_eq_mul] at this

end PositivityTheory.KB.MomentRationality.Ht
