import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupClosedSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleLocality
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleOfPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StandardSmoothLift
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.SmoothStrictTransformComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformAvoidance
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.ChartIsolation
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.ClosedImmersionCommutation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.RadicalCenterIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineEmbeddingIntoAffineSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineSpaceSmooth
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GenericPointsAvoidCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrictTransformTower
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.PrincipalizationWithRadicalCenters
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedCenterFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedLocusFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InactiveTotalSpaceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.FieldExtensionEtaleCover
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsOpenImmersion
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.IrreducibleComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.SmoothOrderOneCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.RestrictionToOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealGeometry
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealAssignment
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SmoothComponentsDisjoint
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.StrictTransformClosedImmersion
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Prepend
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.CartierDivisorComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceDescentDatum
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsWithoutUnitIdeals
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.AffineSpaceCoordinateBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedPullbackSquare
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCasePrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialBlowupIteration
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BlowupAtMonomialCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IrreducibleComponentsOfSupport
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPartAlongDivisor
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ConcatComparisonMap
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.CompanionIdealReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedSchemeWithCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.InvarianceUnderIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderAlongBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.RecursivePrincipalizationPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MaxOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialFactorTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ExceptionalMonomialOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CoordinateSubspaceIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IrreducibleComponentsFlatPreimage
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.SpanSingletonProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.AffineSpaceJacobson
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.GermRegularParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.MaximalContactCover
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianChartChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothHypersurfaceLocalCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsChartNormalization
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AdaptedParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IdealSheafFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardUniqueness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SubschemeMapFlatness
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientCenterImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivationOfSurjective
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.StrictNormalCrossingsMoveToFront
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LogDerivIdealEstimate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.RestrictedBlowupEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealAfterBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientEmbeddingCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PrependedAmbientSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransformOffCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFiberProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.EtaleMaxContactComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactChartUniqueness
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.TaylorExpansion
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusAfterReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.AppendIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SameNontrivialBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LevelwiseIso
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupCartier
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupChartPreimages
import Development.ResolutionOfSingularities.Foundations.Blowup.ReesGrading
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.WeakTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SmoothPullbackMaxContactCover
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
An open immersion is locally of finite presentation and induces isomorphisms on stalks. Each stalk map is formally smooth, so every point of the open lies in the smooth locus of the inclusion. The inclusion is therefore smooth.
-/
private theorem smooth_opens_ι {X : Scheme.{u}} (U : X.Opens) :
    AlgebraicGeometry.Smooth U.ι := by
  rw [← AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff]
  refine le_antisymm le_top ?_
  intro x _
  exact (RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso _) :
    (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap U.ι x)).FormallySmooth)

/- English proof (authored)
Every point of the given open maps to a point at which the structural morphism has formally smooth stalk map. The open inclusion induces an isomorphism on stalks, hence a formally smooth map. Their composite is the stalk map of the restricted morphism and is formally smooth. Since the restricted morphism is locally of finite presentation, this proves smoothness.
-/
private theorem smooth_ι_comp_of_le_smoothLocus {X Z : Scheme.{u}} (f : X ⟶ Z)
    [AlgebraicGeometry.LocallyOfFinitePresentation f] (U : X.Opens)
    (hU : U ≤ AlgebraicGeometry.Scheme.Hom.smoothLocus f) :
    AlgebraicGeometry.Smooth (U.ι ≫ f) := by
  rw [← AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff]
  refine le_antisymm le_top ?_
  intro x _
  have hx : (CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.Hom.stalkMap f (U.ι x))).FormallySmooth := hU x.2
  have hg : (CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.Hom.stalkMap U.ι x)).FormallySmooth :=
    RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have heq : (CommRingCat.Hom.hom
        (AlgebraicGeometry.Scheme.Hom.stalkMap (U.ι ≫ f) x)).FormallySmooth =
      (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap f (U.ι x) ≫
        AlgebraicGeometry.Scheme.Hom.stalkMap U.ι x)).FormallySmooth :=
    congrArg (fun φ => (CommRingCat.Hom.hom φ).FormallySmooth)
      (AlgebraicGeometry.Scheme.Hom.stalkMap_comp U.ι f x)
  exact Eq.mpr heq (RingHom.FormallySmooth.comp hx hg)

/- English proof (authored)
The closed complement consists exactly of the points that do not belong to the smooth locus.
-/
private theorem mem_smoothLocusComplement_iff {X Z : Scheme.{u}} (f : X ⟶ Z)
    [AlgebraicGeometry.LocallyOfFinitePresentation f] (x : ↥X) :
    x ∈ (↑(smoothLocusComplement f) : Set ↥X) ↔
      x ∉ (↑(AlgebraicGeometry.Scheme.Hom.smoothLocus f) : Set ↥X) :=
  Iff.rfl

/- English proof (authored)
Restriction of the closed immersion to the target open is a pullback square along the open inclusion. The flat base-change formula for kernel ideals identifies the new kernel with the original kernel pulled back to that open.
-/
private theorem ker_morphismRestrict {X W : Scheme.{u}} (f : X ⟶ W)
    [AlgebraicGeometry.IsClosedImmersion f] (V : W.Opens) :
    AlgebraicGeometry.Scheme.Hom.ker (f ∣_ V) =
      (AlgebraicGeometry.Scheme.Hom.ker f).comap V.ι :=
  OpenImmersionRestriction.ker_eq_comap_ker_of_isPullback_isOpenImmersion f V.ι (f ∣_ V) ((f ⁻¹ᵁ V).ι)
    (AlgebraicGeometry.isPullback_morphismRestrict f V).flip

/- English proof (authored)
The shortened induced sequence is defined by first constructing the full induced sequence and then deleting the unit-center blowups.
-/
private theorem inducedBlowupsWithoutIso_eq_withoutIsoBlowups {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : EmbeddedBlowupSequence k Y pY)
    (h : S.TransitionsAreBlowups) : S.inducedBlowupsWithoutIso h = (S.inducedBlowups h).withoutIsoBlowups := rfl

private noncomputable def restrictEmbeddingDatumBasicOpen {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsnc : NilIsStrictNormalCrossingsOfSmooth.{u}) (r : Γ(D.ambient, ⊤)) :
    EmbeddingDatum k (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) where
  ambient := (D.ambient.basicOpen r).toScheme
  ambientStruct := (D.ambient.basicOpen r).ι ≫ D.ambientStruct
  emb := D.emb ∣_ D.ambient.basicOpen r
  isAffine_ambient := (AlgebraicGeometry.isAffineOpen_top D.ambient).basicOpen r
  smooth_ambientStruct := by
    have := D.smooth_ambientStruct
    have := smooth_opens_ι (D.ambient.basicOpen r)
    infer_instance
  locallyOfFiniteType_ambientStruct := inferInstance
  quasiCompact_ambientStruct := by
    have : AlgebraicGeometry.IsAffine (D.ambient.basicOpen r).toScheme :=
      (AlgebraicGeometry.isAffineOpen_top D.ambient).basicOpen r
    exact inferInstance
  isClosedImmersion_emb := inferInstance
  nonzeroOnComponents_ker := by
    rw [ker_morphismRestrict]
    exact D.nonzeroOnComponents_ker.comap_of_isOpenImmersion _
  comp_eq := by
    rw [← Category.assoc, AlgebraicGeometry.morphismRestrict_ι, Category.assoc, D.comp_eq]
  sncEmpty := by
    have := D.smooth_ambientStruct
    have := smooth_opens_ι (D.ambient.basicOpen r)
    exact hsnc k _ _ inferInstance

/- English proof (authored)
The ambient morphism is smooth over the field and the new embedding is the pullback of the original one along it. These are the hypotheses of the smooth compatibility theorem for the embedded resolution rule constructed from functorial principalization. The theorem gives the required pullback of sequences along the induced morphism of embedded schemes.
-/
private theorem isPullbackSeq_of_smooth
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (k : Type u) [Field k] [CharZero k] (Y Y' : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (p' : Y' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType p'] [AlgebraicGeometry.QuasiCompact p']
    [AlgebraicGeometry.IsReduced Y'] [AlgebraicGeometry.IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (φ : D'.ambient ⟶ D.ambient) (hsmφ : AlgebraicGeometry.Smooth φ) (ψ : Y' ⟶ Y)
    (hφ : φ ≫ D.ambientStruct = D'.ambientStruct)
    (hsq : IsPullback D'.emb ψ φ D.emb) :
    IsPullbackBlowupSequence ψ (embeddedResolutionRuleOfPrincipalization A hw k Y' p' D')
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have := hsmφ
  exact embeddedResolutionRule_isPullbackBlowupSequence_of_smooth A hA hw k Y Y' p p' D D' φ ψ hφ hsq

/- English proof (authored)
A point in the support of an original center shows that its ideal is nonunit, since the unit ideal has empty support. The corresponding step is retained in the shortened sequence. The shortened center and its projection to the base are the original center and projection at that index. The shortened sequence’s center condition therefore applies to the given point.
-/
private theorem centersLieOver_of_withoutIsoBlowups {X : Scheme.{u}} (s : SequenceOfBlowups X) (Z : Set ↥X)
    (h : s.withoutIsoBlowups.CentersLieOver Z) : s.CentersLieOver Z := by
  intro i hi x hx
  have hne : s.center i ≠ ⊤ := by
    intro h0
    have h1 : (s.center i).support = ⊥ :=
      (AlgebraicGeometry.Scheme.IdealSheafData.support_eq_bot_iff _).mpr h0
    have h2 : x ∈ ((⊥ : TopologicalSpace.Closeds ↥(s.schemeAt i)) : Set ↥(s.schemeAt i)) := by
      rw [← h1]; exact hx
    exact h2
  obtain ⟨j, hj, hji⟩ := s.exists_nontrivialIndex_eq_of_center_ne_top hi hne
  subst hji
  have h1 := h j (by rw [SequenceOfBlowups.withoutIsoBlowups_length]; exact hj) x
    (by rw [SequenceOfBlowups.withoutIsoBlowups_center]; exact hx)
  rwa [SequenceOfBlowups.withoutIsoBlowups_projectionToBase] at h1

/- English proof (authored)
Replace the first embedded sequence by the equal second one. The certificates that its transitions are blowups prove the same proposition and do not change the induced sequence data or the center condition.
-/
private theorem blowupSequence_centersLieOver_congr {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] {S T : EmbeddedBlowupSequence k Y pY} (e : S = T)
    (hS : S.TransitionsAreBlowups) (hT : T.TransitionsAreBlowups) (Z : Set ↥Y)
    (h : (S.inducedBlowups hS).CentersLieOver Z) : (T.inducedBlowups hT).CentersLieOver Z := by
  subst e
  exact h

/- English proof (authored)
The datum identifies the structural morphism with the closed immersion into the ambient scheme followed by the ambient structural morphism. Both maps are quasi-compact, so their composite is quasi-compact.
-/
private theorem quasiCompact_of_embeddingDatum {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY) :
    AlgebraicGeometry.QuasiCompact pY := by
  rw [← D.comp_eq]
  infer_instance

/- English proof (authored)
The detached locus is open by canonical chart isolation and is closed because the strict transform is Noetherian. A point on the support of the center off the detached locus maps into the ambient center. For a smooth original scheme, the component isolation theorem puts every such point in the detached locus. But the support of the center off that locus lies in its complement. This contradiction proves the support is empty and the ideal is the unit ideal.
-/
theorem centerOffDetached_eq_top_of_smooth
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY) (t : ℕ)
    (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length) :
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).centerOffDetached t = ⊤ := by
  have : AlgebraicGeometry.QuasiCompact pY := quasiCompact_of_embeddingDatum D
  have hiso := OpenImmersionRestriction.detachedLocusIsOpen_toEmbeddedBlowupSequence OpenImmersionRestriction.idealSheafGeometryHypotheses_vanishingIdealAssignment hres hB hrad
    (OpenImmersionRestriction.chartIsolationHypotheses_reducedVanishingAssignment (canonicalPrincipalization hres hrad)) k Y pY D
  have hnoe : NoetherianSpace
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t) :=
    EmbeddedBlowupSequence.noetherianSpace_strictTransform_of_isNoetherian _
      (EmbeddedBlowupSequence.isNoetherian_schemeAt (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad))) t
      (le_of_lt ht)
  have hopen : IsOpen ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedLocus t) :=
    hiso t ht
  apply (Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).mpr
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  have h1 := EmbeddedBlowupSequence.support_centerOffDetached_subset_preimage
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) t hy
  have h2 : y ∈ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedLocus t :=
    OpenImmersionRestriction.mem_detachedLocus_of_mem_support_ambientCenter hres hB hrad D hsm t ht y h1
  have h3 := EmbeddedBlowupSequence.support_centerOffDetached_subset_detachedClosureCompl
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) t hnoe hopen hy
  rw [EmbeddedBlowupSequence.detachedClosureCompl_coe, EmbeddedBlowupSequence.detachedClosure_coe] at h3
  exact h3 h2

/- English proof (authored)
For a smooth input the center off the detached locus is the unit ideal, so it defines the empty subscheme. The total-space center is the kernel of the map from that subscheme into the total space. A map from an empty scheme has unit kernel, giving the result.
-/
theorem toEmbeddedBlowupSequence_center_eq_top_of_smooth
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY)
    (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups) (t : ℕ)
    (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).center t = ⊤ := by
  rw [EmbeddedBlowupSequence.inducedBlowups_center, EmbeddedBlowupSequence.totalCenter_eq,
    centerOffDetached_eq_top_of_smooth hres hB hrad D hsm t ht]
  exact AlgebraicGeometry.Scheme.ker_eq_top_of_isEmpty ..

/- English proof (authored)
Every induced center is the unit ideal for a smooth input. If the shortened sequence had positive length, its first retained center would be nonunit and would come from a step within the original length. This contradicts the unit-center result, so the shortened length is zero.
-/
private theorem withoutIsoBlowups_length_eq_zero_of_smooth
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY)
    (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).lengthWithoutIsoBlowups = 0 := by
  by_contra hne
  have h0 : 0 < ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).lengthWithoutIsoBlowups :=
    Nat.pos_of_ne_zero hne
  have h1 := SequenceOfBlowups.nontrivialIndex_lt_length _ h0
  have h2 := SequenceOfBlowups.center_nontrivialIndex_ne_top _ h0
  rw [EmbeddedBlowupSequence.inducedBlowups_length] at h1
  exact h2 (toEmbeddedBlowupSequence_center_eq_top_of_smooth hres hB hrad D hsm hbl _ h1)

/- English proof (authored)
Suppose a center point projects to the smooth locus of the original affine scheme. Since the embedding is closed, that smooth locus is the inverse image of an ambient open. Choose an ambient basic open through the image point contained in that ambient open. Its inverse image in the original scheme is affine and smooth over the field. Restrict the embedding datum to these opens. The ambient inclusion is smooth, so compatibility of the embedded rule identifies its sequence on this chart with the pullback of the original sequence, with empty centers deleted. The chart sequence has length zero because its source is smooth. Yet the given center point lifts to a point in the support of the pulled-back center over the chart, and such a nonempty center must be retained. This would give a step of the length-zero sequence, a contradiction.
-/
private theorem centersLieOver_embeddedResolutionRuleOfPrincipalization
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    (hA : IsFunctorialPrincipalization (canonicalPrincipalization hres hrad))
    (hw : TransitionsAreBlowupsForEmbeddings (canonicalPrincipalization hres hrad))
    (hsnc : NilIsStrictNormalCrossingsOfSmooth.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFinitePresentation pY]
    (D : EmbeddingDatum k Y pY) :
    (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).CentersLieOver
      (↑(smoothLocusComplement pY) : Set ↥Y) := by
  intro i hi x hx
  by_contra hns
  have hy : (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
      (↑(AlgebraicGeometry.Scheme.Hom.smoothLocus pY) : Set ↥Y) := by
    by_contra h
    exact hns ((mem_smoothLocusComplement_iff pY _).mpr h)
  obtain ⟨W, hWopen, hW⟩ :=
    ((AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding D.emb).isInducing).isOpen_iff.mp
      (AlgebraicGeometry.Scheme.Hom.smoothLocus pY).isOpen
  have hWy :
      D.emb
        ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x)
        ∈ W := by
    have h2 :
        (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
          ⇑D.emb ⁻¹' W := by
      rw [hW]; exact hy
    exact h2
  obtain ⟨U', hU'mem, hxU', hU'le⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.isBasis_basicOpen D.ambient)
      (show D.emb
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x)
          ∈ (⟨W, hWopen⟩ : D.ambient.Opens) from hWy)
  obtain ⟨r, hr⟩ := hU'mem
  have hyV : (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
      D.emb ⁻¹ᵁ D.ambient.basicOpen r := by
    have h3 :
        D.emb
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x)
          ∈ D.ambient.basicOpen r := by
      rw [hr]; exact hxU'
    exact h3
  have hVle : (D.emb ⁻¹ᵁ D.ambient.basicOpen r) ≤
      AlgebraicGeometry.Scheme.Hom.smoothLocus pY := by
    intro z hz
    have h3 : D.emb z ∈ D.ambient.basicOpen r := hz
    rw [hr] at h3
    have h5 : z ∈ ⇑D.emb ⁻¹' W := hU'le h3
    rw [hW] at h5
    exact h5
  have hVaff : AlgebraicGeometry.IsAffine (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme :=
    ((AlgebraicGeometry.isAffineOpen_top D.ambient).basicOpen r).preimage D.emb
  have hsmV : AlgebraicGeometry.Smooth ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) :=
    smooth_ι_comp_of_le_smoothLocus pY _ hVle
  have hqcV : AlgebraicGeometry.QuasiCompact ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) :=
    inferInstance
  have hlen0 : (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k
      (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) (restrictEmbeddingDatumBasicOpen D hsnc r)).length = 0 := by
    rw [embeddedResolutionRuleOfPrincipalization_apply, inducedBlowupsWithoutIso_eq_withoutIsoBlowups, SequenceOfBlowups.withoutIsoBlowups_length]
    exact withoutIsoBlowups_length_eq_zero_of_smooth hres hB hrad (restrictEmbeddingDatumBasicOpen D hsnc r) hsmV _
  have hps := isPullbackSeq_of_smooth (canonicalPrincipalization hres hrad) hA hw k Y
      (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme pY
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) D (restrictEmbeddingDatumBasicOpen D hsnc r)
      (D.ambient.basicOpen r).ι (smooth_opens_ι (D.ambient.basicOpen r))
      (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι rfl
      (AlgebraicGeometry.isPullback_morphismRestrict D.emb (D.ambient.basicOpen r))
  obtain ⟨ρ, e, h1, h2, h3, h4, h5, h6, h7⟩ := hps
  have hmemrange :
      (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
        Set.range ⇑(D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    exact hyV
  obtain ⟨x', hx'eq⟩ := hmemrange
  obtain ⟨z, hz1, hz2⟩ :=
    AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (f := (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι)
      (g := (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i)
      x' x hx'eq
  have hex : ∃ w, w ∈
      (((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).center i).comap
        (Limits.pullback.snd (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase
            i))).support := by
    refine ⟨z, ?_⟩
    have hmem : z ∈
        (↑((((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).center
          i).comap (Limits.pullback.snd (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι
            ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase
              i))).support) : Set _) := by
      rw [FunctorialResolution.EmbeddedResolution.support_comap]
      show (Limits.pullback.snd (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i)) z
          ∈ (↑((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).center
                i).support : Set _)
      rw [hz2]
      exact hx
    exact hmem
  obtain ⟨j, hj, -⟩ := (h4 i hi).mp hex
  rw [hlen0] at hj
  exact absurd hj (Nat.not_lt_zero j)

/- English proof (authored)
The shortened sequence is the embedded resolution rule on the given datum, so every one of its centers lies over the complement of the smooth locus. Every point of an original center belongs to a retained step. The transfer from the shortened sequence thus gives the center condition for the full induced sequence.
-/
theorem toEmbeddedBlowupSequence_centersLieOver_smoothLocusComplement
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    (hA : IsFunctorialPrincipalization (canonicalPrincipalization hres hrad))
    (hw : TransitionsAreBlowupsForEmbeddings (canonicalPrincipalization hres hrad))
    (hsnc : NilIsStrictNormalCrossingsOfSmooth.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFinitePresentation pY]
    (D : EmbeddingDatum k Y pY)
    (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).CentersLieOver
      (↑(smoothLocusComplement pY) : Set ↥Y) := by
  apply centersLieOver_of_withoutIsoBlowups
  have h := centersLieOver_embeddedResolutionRuleOfPrincipalization hres hB hrad hA hw hsnc D
  rw [embeddedResolutionRuleOfPrincipalization_apply] at h
  exact h

/- English proof (authored)
Apply the embedded center avoidance result to the affine-space embedding datum for the canonical principalization with radical centers. Its hypotheses are supplied by correctness and functoriality of the canonical algorithm, radicality of smooth centers, the blowup transition result, and the empty-boundary property for smooth schemes. The embedded sequence formed from the chosen datum agrees with the sequence obtained from the affine-space data. Their induced blowup sequences thus have the same center condition, which puts the affine centers over the singular locus.
-/
theorem affineCentersLieOverSingularLocus_principalizationWithRadicalCenters :
    AffineCentersLieOverSingularLocus.{u} principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters := by
  intro k _ _ Y pY _ _ _ _
  unfold FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.InducedCentersLieOverSingularLocus
  have hbl0 :
      ((affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
          k Y pY).toEmbeddedBlowupSequence principalizationWithRadicalCenters).TransitionsAreBlowups :=
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters k Y pY _
  have key := toEmbeddedBlowupSequence_centersLieOver_smoothLocusComplement strictTransformIsBlowupOfClosedSubscheme
    canonicalAlgorithmRules_isCorrect smoothSubschemeIdealIsRadical
    (isFunctorialPrincipalization_canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme canonicalAlgorithmRules_isCorrect
      smoothSubschemeIdealIsRadical
      (commutesWithClosedImmersion_of_isCorrect (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme) canonicalAlgorithmRules_isCorrect))
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters nilIsStrictNormalCrossingsOfSmooth
    (affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
      k Y pY) hbl0
  rw [← AffineSpacePrincipalizationData.embeddedInducedBlowups_eq]
  exact blowupSequence_centersLieOver_congr
    (affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth k Y pY) hbl0 _ _ key

end FunctorialResolution.EmbeddedResolution
