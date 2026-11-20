import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem exists_pdPoly : ∀ (B : Type) [CommRing B], Nonempty (PDPoly B) :=
  fun B _ ↦ ⟨stdPoly B⟩

end GlobalTheory
