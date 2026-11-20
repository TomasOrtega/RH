import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LowerBound
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Comparison
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseBoundedHeight
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DegreeTopEqArithDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
The claim follows from `heightLowerBound`.
-/
theorem HeightLowerBound.main : HeightLowerBound.Statement := heightLowerBound

/- English proof (translation)
The claim follows from `heightMetricChange`.
-/
theorem HeightMetricChange.main : HeightMetricChange.Statement := heightMetricChange

/- English proof (translation)
The claim follows from `heightLocalAgreement`.
-/
theorem HeightLocalAgreement.main : HeightLocalAgreement.Statement := heightLocalAgreement

/- English proof (translation)
The claim follows from `heightPullback`.
-/
theorem HeightPullback.main : HeightPullback.Statement := heightPullback

/- English proof (translation)
The claim follows from `heightComparison`.
-/
theorem HeightComparison.main : HeightComparison.Statement := heightComparison

/- English proof (translation)
The claim follows from `denseBoundedHeight`.
-/
theorem DenseBoundedHeight.main : DenseBoundedHeight.Statement := denseBoundedHeight

/- English proof (translation)
The claim follows from `slopeMaxExtension`.
-/
theorem SlopeMaxExtension.main : SlopeMaxExtension.Statement := slopeMaxExtension

/- English proof (translation)
The claim follows from `flagDegreeBound`.
-/
theorem FlagDegreeBound.main : FlagDegreeBound.Statement := flagDegreeBound

end GroundTheory.Heights₂.Heights
