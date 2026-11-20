import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory

/- English proof (translation)
The claim follows from `fun B _ ↦ ⟨stdPoly B⟩`.
-/
theorem exists_pdPoly : ∀ (B : Type) [CommRing B], Nonempty (PDPoly B) :=
  fun B _ ↦ ⟨stdPoly B⟩

end GlobalTheory
