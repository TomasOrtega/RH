import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupClosedSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleLocality
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GluedBlowupSequenceExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StandardSmoothLift
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformAvoidance
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.ChartIsolation
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.RestrictionToOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealAssignment
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.ClosedImmersionCommutation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.CanonicalDivisorReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalRulesCorrect
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.RadicalCenterIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineEmbeddingIntoAffineSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineSpaceSmooth
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The correctness theorem for canonical rules assumes that strict transforms are the blowups of the corresponding closed subschemes. This compatibility is available, so the rules reduce inductively on dimension.
-/
theorem canonicalAlgorithmRules_isCorrect :
    (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme.{u}).ReducesInductivelyOnDimension :=
  isCorrect_canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme

noncomputable abbrev principalizationWithRadicalCenters : PrincipalizationAlgorithm.{u} :=
  canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme smoothSubschemeIdealIsRadical.{u}

/- English proof (authored)
For the given affine input, form the specified embedding into affine space. The discarded locus at any stage is the detached locus for these embedding data. The assumed openness of detached loci for every embedding applies to this one.
-/
theorem embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen (A : PrincipalizationAlgorithm.{u}) (h : DetachedLocusIsOpenForEmbeddings.{u} A) :
    EmbeddedPrincipalizationDiscardedLocusIsOpen.{u} A affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth := by
  intro k _ _ Y pY _ _ _ _ i hi
  exact h k Y pY
    (affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace
      affineSpaceIsSmooth k Y pY) i hi

/- English proof (authored)
Both vanishing assignments send a closed set to its reduced vanishing ideal. They are therefore equal pointwise. Apply the chart isolation result for the reduced assignment to this principalization algorithm and use the equality of assignments.
-/
theorem chartIsolationHypotheses_principalizationWithRadicalCenters :
    OpenImmersionRestriction.ChartIsolationHypotheses OpenImmersionRestriction.vanishingIdealAssignment.{u} principalizationWithRadicalCenters.{u} := by
  have h : OpenImmersionRestriction.reducedVanishingAssignment.{u} = OpenImmersionRestriction.vanishingIdealAssignment.{u} := by
    funext X T
    rw [OpenImmersionRestriction.vanishingIdealAssignment_apply]
    rfl
  have h2 := OpenImmersionRestriction.chartIsolationHypotheses_reducedVanishingAssignment principalizationWithRadicalCenters.{u}
  rwa [h] at h2

/- English proof (authored)
The canonical openness theorem applies using strict-transform compatibility, correctness of the canonical reduction, radicality of smooth subscheme ideals, and the chart isolation hypotheses for the vanishing-ideal assignment. It yields openness of the detached locus at every relevant stage for every embedding.
-/
theorem detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters :
    DetachedLocusIsOpenForEmbeddings.{u} principalizationWithRadicalCenters.{u} :=
  OpenImmersionRestriction.detachedLocusIsOpenForEmbeddings_canonicalPrincipalization OpenImmersionRestriction.idealSheafGeometryHypotheses_vanishingIdealAssignment.{u}
    strictTransformIsBlowupOfClosedSubscheme.{u} canonicalAlgorithmRules_isCorrect smoothSubschemeIdealIsRadical.{u}
    chartIsolationHypotheses_principalizationWithRadicalCenters.{u}

/- English proof (authored)
Every detached locus is open for this principalization algorithm by the canonical openness result. The construction that separates the detached components then identifies the embedding transitions as blowups.
-/
theorem transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters :
    TransitionsAreBlowupsForEmbeddings principalizationWithRadicalCenters.{u} :=
  transitionsAreBlowupsForEmbeddings_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
    detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters

/- English proof (authored)
The chosen affine embeddings have open discarded loci by detached-locus openness, and their ambient stages are Noetherian. Strict transforms satisfy the expected closed-subscheme blowup compatibility. The theorem constructing blowups from these data therefore applies to the embedded principalization sequence.
-/
theorem embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters :
    EmbeddedPrincipalizationYieldsBlowups principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
  embeddedPrincipalizationYieldsBlowups_of_discardedLocusIsOpen principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
    (embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
      detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters)
    (embeddedPrincipalizationAmbientIsNoetherian principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    strictTransformIsBlowupOfClosedSubscheme

/- English proof (authored)
Apply the functoriality theorem for canonical principalization. Its hypotheses follow from strict-transform compatibility, correctness of the dimension reduction, radicality of smooth subscheme ideals, and the closed-immersion commutation theorem for correct rules.
-/
theorem isFunctorialPrincipalization_principalizationWithRadicalCenters : IsFunctorialPrincipalization principalizationWithRadicalCenters.{u} :=
  isFunctorialPrincipalization_canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme canonicalAlgorithmRules_isCorrect
    smoothSubschemeIdealIsRadical
    (commutesWithClosedImmersion_of_isCorrect (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme) canonicalAlgorithmRules_isCorrect)

noncomputable def canonicalAffineResolutionRule : AffineResolutionRule.{u} :=
  affineResolutionRuleOfPrincipalization principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters

end FunctorialResolution.EmbeddedResolution
