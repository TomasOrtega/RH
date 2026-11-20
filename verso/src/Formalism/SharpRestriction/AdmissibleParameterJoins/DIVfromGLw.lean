import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

/- English proof (translation)
Assemble the required witnesses or components as `⟨hK, fun u => by obtain ⟨_, _, _, ⟨h, _⟩, _⟩ := h6 u exact h⟩`.
-/
theorem kernels_rational_over_coefficients (D : D7) (hK : StandardLatticesGL3.kRat D) (h6 : ∀ u, product_first_zeroth_parts.Conclusion6 D u) : LocalQuadraticParts.KernelRationality D :=
  ⟨hK, fun u => by
    obtain ⟨_, _, _, ⟨h, _⟩, _⟩ := h6 u
    exact h⟩

end Formalism.MainNotions.J

end
