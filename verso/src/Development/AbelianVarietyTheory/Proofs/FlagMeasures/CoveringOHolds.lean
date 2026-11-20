import Mathlib
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransferenceCoverHolds

namespace GlobalTheory

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem coveringO_holds : Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO := by
  apply Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.coveringO_of_transference
  intro E _ _ _ Λ _ _ lam hlam hdual x
  exact transferenceCover_holds E Λ lam hlam hdual x

end GlobalTheory
