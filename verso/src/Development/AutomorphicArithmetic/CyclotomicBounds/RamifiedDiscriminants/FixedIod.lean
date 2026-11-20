import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.PrimeDiscriminants.CycImage

open NumberField Formalism.BasicNotions

namespace UpperTheory.Ram

/- English proof (translation)
Use `H.toHostRaw.image_mem_of_fixed J M (Dvd.intro _ rfl) hM x fun u hu => ?_` and prove the remaining obligations. Break down `H.art_d u hu with h | h` into its components or cases. Rewrite using `[h, map_one]`. Both sides reduce to the same expression. Rewrite using `[h]`.

Conclude with `hx`.
-/
theorem image_mem_of_fixed_iod {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) (M : Subfield Ω)
    (hM : ∀ y : Ω, y ^ (H.QS * H.q) = 1 → y ∈ M) (x : H.E) (hx : H.sigmaOf R.toFrame.iod x = x) : J x ∈ M := by
  refine H.toHostRaw.image_mem_of_fixed J M (Dvd.intro _ rfl) hM x fun u hu => ?_
  rcases H.art_d u hu with h | h
  · rw [h, map_one]; rfl
  · rw [h]; exact hx

end UpperTheory.Ram
