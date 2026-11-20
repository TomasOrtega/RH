import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutSpecialize
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChart
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChartSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutPreimage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

/- English proof (translation)
The claim follows from `SegreFlagCutDivisor.proof SegreFlagCutSpecialize.proof (SegreFlagCutChart.proof SegreFlagCutChartSection.proof SegreFlagCutPreimage.proof)`.
-/
theorem SegreFlagCutDivisor.closed : SegreFlagCutDivisor.Statement :=
  SegreFlagCutDivisor.proof SegreFlagCutSpecialize.proof
    (SegreFlagCutChart.proof SegreFlagCutChartSection.proof SegreFlagCutPreimage.proof)

end GroundTheory.Heights₂.Heights.NumbersDVR
