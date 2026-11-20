import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.KleimanFibreHilbertFlat
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.PuncturedBranchInOneBranch
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPuncturedBranchSameOrder
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedGeneral
set_option maxSynthPendingDepth 1

/- English proof (translation)
The claim follows from `@GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder.proof GroundTheory.Heights₂.Heights.AutoClose.PuncturedCurveDiscInverse`.
-/
theorem GroundTheory.Heights₂.Heights.AutoClose.PuncturedBranchSameOrder : GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder.Statement :=
  @GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder.proof GroundTheory.Heights₂.Heights.AutoClose.PuncturedCurveDiscInverse
