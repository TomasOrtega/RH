import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.CentredDiscCoverCurveHolds
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSliceSheetParam
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImageDimLe
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenPolyFull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCountPrime
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSameOrdersLiftCentre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
set_option maxSynthPendingDepth 1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GroundTheory.Heights₂.Heights.AutoClose.IsolatedPointsCountPrime : GroundTheory.Heights₂.Heights.IsolatedPointsCountPrime.Statement :=
  @GroundTheory.Heights₂.Heights.IsolatedPointsCountPrime.proof GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly.full GroundTheory.Heights₂.Heights.AutoClose.DominantFibreBound GroundTheory.Heights₂.Heights.ImageDimLe.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GroundTheory.Heights₂.Heights.AutoClose.SameOrdersLiftCentre : GroundTheory.Heights₂.Heights.SameOrdersLiftCentre.Statement :=
  @GroundTheory.Heights₂.Heights.SameOrdersLiftCentre.proof GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GroundTheory.Heights₂.Heights.AutoClose.ConeSliceSheetParam : GroundTheory.Heights₂.Heights.ConeSliceSheetParam.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSliceSheetParam.proof GroundTheory.Heights₂.Heights.AutoClose.DiscriminantSheetCover
