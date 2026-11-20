import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.InjectiveHolomorphicJacobianNeZeroHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.RegularLocusIdentityHolds
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimDomain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBundleRadicalAway
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMultGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedAwayZariski
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceUnmixedGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTransverseSliceGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedAway
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLength
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchesHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CurveBranchLengthHoldsStatement
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Heights.BranchOrder

open GroundTheory.Heights₂.Heights

/- English proof (translation)
The claim follows from `@SliceReducedAwayZariski.proof AutoClose.GenericFibreRadicalAway SliceBundleRadicalAway.proof`.
-/
theorem sliceReducedAwayZariski : SliceReducedAwayZariski.Statement :=
  @SliceReducedAwayZariski.proof AutoClose.GenericFibreRadicalAway SliceBundleRadicalAway.proof

/- English proof (translation)
The claim follows from `@SliceReducedAway.proof sliceReducedAwayZariski`.
-/
theorem sliceReducedAway : SliceReducedAway.Statement :=
  @SliceReducedAway.proof sliceReducedAwayZariski

/- English proof (translation)
The claim follows from `@SliceUnmixedGeneral.proof AutoClose.CMHeightOneGeneral LocalDimDomain.proof AutoClose.SliceLocalDimGeneral AutoClose.SliceCMUnmixed`.
-/
theorem sliceUnmixedGeneral : SliceUnmixedGeneral.Statement :=
  @SliceUnmixedGeneral.proof AutoClose.CMHeightOneGeneral LocalDimDomain.proof
    AutoClose.SliceLocalDimGeneral AutoClose.SliceCMUnmixed

/- English proof (translation)
The claim follows from `@SliceReducedGeneral.proof sliceUnmixedGeneral sliceReducedAway`.
-/
theorem sliceReducedGeneral : SliceReducedGeneral.Statement :=
  @SliceReducedGeneral.proof sliceUnmixedGeneral sliceReducedAway

/- English proof (translation)
The claim follows from `@SliceMultGeneral.proof AutoClose.CMGeneralPoint TransverseSliceGeneral.proof AutoClose.LengthTransverseSlice`.
-/
theorem sliceMultGeneral : SliceMultGeneral.Statement :=
  @SliceMultGeneral.proof AutoClose.CMGeneralPoint TransverseSliceGeneral.proof AutoClose.LengthTransverseSlice

/- English proof (translation)
The claim follows from `@SliceLength.proof IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.full sliceReducedGeneral sliceMultGeneral`.
-/
theorem sliceLength : SliceLength.Statement :=
  @SliceLength.proof IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.full sliceReducedGeneral sliceMultGeneral

/- English proof (translation)
The claim follows from `LocalOrder.proof sliceLength GlobalTheory.T.slice_branches_holds GlobalTheory.T.curve_branch_length_holds`.
-/
theorem localOrder : LocalOrder.Statement :=
  LocalOrder.proof sliceLength GlobalTheory.T.slice_branches_holds GlobalTheory.T.curve_branch_length_holds

end GlobalTheory.CompanionTheory.Heights.BranchOrder
