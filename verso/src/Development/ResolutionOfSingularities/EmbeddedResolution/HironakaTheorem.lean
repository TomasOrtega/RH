import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsClopen
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineCentersOverSingularLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineEmbeddingIntoAffineSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineDetachedConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineSpaceSmooth
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineBoundaryStrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SmoothLocusPreimageDense
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SingularPreimageBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GlobalResolutionFromAffine
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.PrincipalizationWithRadicalCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.ClosedEmbeddingsIntoAffineSpace
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Embed the affine input in smooth affine space with empty boundary and apply canonical principalization to its embedding ideal. The radical-center construction gives open detached loci and induced blowup transitions. Functorial principalization ends with the unit ideal, so no strict-transform component remains at the final stage. Each discarded piece is smooth, and the preimage of the original smooth locus is dense there. The induced centers lie over the singular locus. The reduced inverse image of that locus on each discarded piece is described by the ambient boundary, with the discarded pieces open and closed in the relevant centers and no discarded component contained in a boundary member. The ambient stages are smooth, their boundaries have strict normal crossings, and each ambient center meets the boundary in strict normal crossings. The restriction result gives strict normal crossings on the discarded pieces, while properness comes from the blowups. These are the hypotheses of the affine criterion for the induced sequence after the unit-center steps are removed. That criterion gives strong resolution for the canonical affine rule.
-/
theorem isStrongResolution_canonicalAffineResolutionRule (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] :
    IsStrongResolution k Y p (canonicalAffineResolutionRule k Y p) := by
  have hIso : EmbeddedPrincipalizationDiscardedLocusIsOpen principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
    embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
      detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters
  have hsmooth : AffineDetachedSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
    affineDetachedSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
  have hCen : AffineCentersLieOverSingularLocus principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters :=
    affineCentersLieOverSingularLocus_principalizationWithRadicalCenters
  show IsStrongResolution k Y p
    (affineResolutionRuleOfPrincipalization principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters k Y p)
  exact isStrongResolution_blowupSequenceWithoutIsos_ofAffine principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters
    (affineStrictTransformEmptyAtLast_of_isFunctorialPrincipalization principalizationWithRadicalCenters.{u}
      isFunctorialPrincipalization_principalizationWithRadicalCenters affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace
      affineSpaceIsSmooth)
    hsmooth
    (affineSmoothLocusPreimageDenseInDetached principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    hCen
    (affineDetachedClopenInCenter principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineDetachedComponentsNotInBoundary principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineDetachedSingularPreimageEqBoundary_of_centersLieOverSing principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth hIso hsmooth
      embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters hCen)
    (affineCentersHaveStrictNormalCrossingsWithBoundary principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineAllLevelsSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineBoundaryInStrictNormalCrossingPosition principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    strictNormalCrossingsRestrictToClopen Blowup.blowupIsProper k Y p

/- English proof (authored)
Use the canonical principalization algorithm with radical centers. It is functorial, and its induced transitions in the embedded construction are blowups. Every affine input embeds in smooth affine space with empty boundary, and any two such closed embeddings can be compared by an automorphism after introducing the other set of coordinates. The canonical affine rule is a strong resolution by the affine criterion. The globalization theorem for principalization applies to these data, giving a strong resolution rule in characteristic zero with the required smooth pullback and field extension compatibilities.
-/
theorem strongResolutionOfSingularitiesCharZero :
    StrongResolutionOfSingularitiesCharZero.{u} :=
  strongResolutionOfSingularitiesCharZero_of_principalizationAlgorithm principalizationWithRadicalCenters.{u}
    affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
    isFunctorialPrincipalization_principalizationWithRadicalCenters
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters
    embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters
    closedEmbeddingsRelatedByAutomorphism
    isStrongResolution_canonicalAffineResolutionRule

end FunctorialResolution.EmbeddedResolution
