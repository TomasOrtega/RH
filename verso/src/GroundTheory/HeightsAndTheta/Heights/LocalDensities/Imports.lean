import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.LeviFormGbPotOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h n A A' hA`. Conclude with `h n A A' hA.1 hA.2`. Introduce `h n A B hB hAB`. Conclude with `h n A B ⟨hB, hAB⟩`.
-/
theorem DetMono.equiv :
    FourB.HermitianDetMono.Statement ↔ IndefiniteRowSideFullHecke.FourB.DetMono.Statement := by
  constructor
  · intro h n A A' hA
    exact h n A A' hA.1 hA.2
  · intro h n A B hB hAB
    exact h n A B ⟨hB, hAB⟩

end GroundTheory.Heights₂.Heights
