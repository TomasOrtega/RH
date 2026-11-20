import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem ChartVanishing.equiv :
    GroundTheory.Heights₂.Heights.ChartVanishing.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartVanishing.Statement := by
  constructor
  · intro h ι _ _ n P D G z hz c
    exact h ι n P (AddBlockData.toObjects D) G.d G.g G.isFormSystem z hz c
  · intro h ι _ _ n P D d g hg z hz c
    exact h ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem hg) z hz c

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
