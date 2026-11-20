import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
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
