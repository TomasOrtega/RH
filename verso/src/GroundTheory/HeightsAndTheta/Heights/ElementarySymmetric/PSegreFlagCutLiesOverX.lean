import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutLiesOver
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChartSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

/- English proof (translation)
The claim follows from `SegreFlagCutLiesOver.proof SegreFlagCutChartSection.proof`.
-/
theorem SegreFlagCutLiesOver.closed : SegreFlagCutLiesOver.Statement :=
  SegreFlagCutLiesOver.proof SegreFlagCutChartSection.proof

end GroundTheory.Heights₂.Heights.NumbersDVR
