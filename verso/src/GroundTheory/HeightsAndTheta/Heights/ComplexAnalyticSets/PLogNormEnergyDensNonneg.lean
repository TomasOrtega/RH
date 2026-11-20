import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogNormEnergyDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogNormGradDensNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem LogNormEnergyDensNonneg.proof : LogNormEnergyDensNonneg.Statement := by
  intro n d h s y v hs hsy
  exact LogNormGradDensNonneg.proof n d h s y v hs hsy

end GroundTheory.Heights₂.Heights
