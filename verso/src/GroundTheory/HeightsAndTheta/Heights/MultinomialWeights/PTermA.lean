import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.TheoremB

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem TermA.proof : TermA.Statement := by
  intro d S hI9 u hu
  exact mul_nonneg S.vol_pos.le (hI9 u hu).1

end GroundTheory.Heights₂.Heights.TheoremB
