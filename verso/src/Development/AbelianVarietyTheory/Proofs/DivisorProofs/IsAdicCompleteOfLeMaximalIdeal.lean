import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRing
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem isAdicComplete_of_le_maximalIdeal :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      IsAdicComplete (maximalIdeal R) R → ∀ (I : Ideal R), I ≤ maximalIdeal R →
        IsAdicComplete I R := by
  intro R _ _ _ hm I hI
  exact isAdicComplete_of_le_of_isNoetherianRing R I (maximalIdeal R) hI hm

end GlobalTheory
