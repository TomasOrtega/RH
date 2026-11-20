import Formalism.SharpRestriction.SmoothDesignExistence.WithSmOfWithCh
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions

/- English proof (translation)
The claim follows from `Closed.of_class (P := fun Fm _ => flipTwoThree.admF7 Fm) fun Fm _ hc => kRatE_of (h Fm hc)`.
-/
theorem kernel_ratio_closed_of_class {𝒞 : FamClass} (h : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → LLKerE Fm) :
    Closed 𝒞 fun Fm _ => flipTwoThree.admF7 Fm :=
  Closed.of_class (P := fun Fm _ => flipTwoThree.admF7 Fm) fun Fm _ hc => kRatE_of (h Fm hc)

end Formalism.MainNotions.Pk
