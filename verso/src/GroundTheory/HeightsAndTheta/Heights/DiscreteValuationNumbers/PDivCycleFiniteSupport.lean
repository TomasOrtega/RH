import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Introduce `R _ _ K _ ι _ P f`. Apply `Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f}))` to reduce the goal to its premises. Introduce `W hW`. Assume the negation of the conclusion as `hmin`. Apply `hW` to reduce the goal to its premises.

Unfold `divCycle`. Rewrite using `[dif_neg]`. Conclude with `fun h => hmin h.1`.
-/
theorem DivCycleFiniteSupport.proof : DivCycleFiniteSupport.Statement.{u} := by
  intro R _ _ K _ ι _ P f
  apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f}))
  intro W hW
  by_contra hmin
  apply hW
  unfold divCycle
  rw [dif_neg]
  exact fun h => hmin h.1

end GroundTheory.Heights₂.Heights.NumbersDVR
