import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h ι _ _ n P D hD a p hp`. Use `Fact.mk hp` as an intermediate fact. Conclude with `h ι n P D hD a p`. Introduce `h ι _ _ n P D hD a p hp`.

Conclude with `h ι n P D hD a p hp.out`.
-/
theorem WeightedDegree.equiv :
    GroundTheory.Heights₂.Heights.WeightedDegree.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.WeightedDegree.Statement := by
  constructor
  · intro h ι _ _ n P D hD a p hp
    have := Fact.mk hp
    exact h ι n P D hD a p
  · intro h ι _ _ n P D hD a p hp
    exact h ι n P D hD a p hp.out

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
