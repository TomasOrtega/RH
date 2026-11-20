import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange

set_option autoImplicit false

namespace GlobalTheory.Published

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem nefNumerics_of_product_of_riemannRoch
    (h₁ : NefProductNonneg) (h₂ : NefRiemannRoch) : NefNumerics :=
  ⟨h₁, h₂.nefBigIff, h₂⟩

end GlobalTheory.Published
