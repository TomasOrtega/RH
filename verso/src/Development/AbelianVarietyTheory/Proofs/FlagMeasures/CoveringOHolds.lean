import Mathlib
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransferenceCoverHolds

namespace GlobalTheory

/- English proof (translation)
Apply `Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.coveringO_of_transference` to reduce the goal to its premises. Introduce `E _ _ _ Λ _ _ lam hlam hdual x`. Conclude with `transferenceCover_holds E Λ lam hlam hdual x`.
-/
theorem coveringO_holds : Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO := by
  apply Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.coveringO_of_transference
  intro E _ _ _ Λ _ _ lam hlam hdual x
  exact transferenceCover_holds E Λ lam hlam hdual x

end GlobalTheory
