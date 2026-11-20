import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem FlagAntisymHomogeneous.proof : FlagAntisymHomogeneous.Statement := by
  intro f N H d hH
  have hmem : ∀ w : Fin f → Equiv.Perm (Fin N),
      blockSign f N w • blockPermute f N w H ∈ homogeneousSubmodule (Fin f × Fin N) ℚ d := by
    intro w
    refine Submodule.smul_mem _ _ ?_
    rw [mem_homogeneousSubmodule]
    exact hH.rename_isHomogeneous
  have hsum : antisymmetrize f N H ∈ homogeneousSubmodule (Fin f × Fin N) ℚ d :=
    Submodule.sum_mem _ (fun w _ => hmem w)
  rwa [mem_homogeneousSubmodule] at hsum

end RestTerms

end GroundTheory.Heights₂.Heights
