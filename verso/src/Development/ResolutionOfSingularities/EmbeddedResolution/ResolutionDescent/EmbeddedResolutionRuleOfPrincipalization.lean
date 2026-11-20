import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def NilIsStrictNormalCrossingsOfSmooth : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
    (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []

/- English proof (translation)
Introduce `k _ _ A q hq`. Establish `: AlgebraicGeometry.Smooth q` using `hq`. Conclude with `inStrictNormalCrossingPosition_nil q`.
-/
theorem nilIsStrictNormalCrossingsOfSmooth : NilIsStrictNormalCrossingsOfSmooth.{u} := by
  intro k _ _ A q hq
  have : AlgebraicGeometry.Smooth q := hq
  exact inStrictNormalCrossingPosition_nil q

/- English proof (translation)
Introduce `k _ _ Y p _ _ _ _ D i hi`. Establish `hi' : i < ((D.toEmbeddedBlowupSequence A).inducedBlowups (h k Y p D)).withoutIsoBlowups.length` using `hi`. Conclude with `SequenceOfBlowups.withoutIsoBlowups_center_ne_top _ hi'`.
-/
theorem hasProperCenters_embeddedResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A) :
    (embeddedResolutionRuleOfPrincipalization A h).HasProperCenters := by
  intro k _ _ Y p _ _ _ _ D i hi
  have hi' : i < ((D.toEmbeddedBlowupSequence A).inducedBlowups (h k Y p D)).withoutIsoBlowups.length := hi
  exact SequenceOfBlowups.withoutIsoBlowups_center_ne_top _ hi'

/- English proof (translation)
Use function extensionality and compare the values at `k _ _ Y p _ _ _ _`. Rewrite using `[EmbeddedResolutionRule.toAffineResolutionRule_apply, affineSpaceEmbeddingChoice_eq_affineSpaceEmbeddingDatum]`. Conclude with `embeddedResolutionRuleOfPrincipalization_affineSpaceEmbeddingDatum A h hemb hsnc hsm hw k Y p`.
-/
theorem toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hw : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm) :
    (embeddedResolutionRuleOfPrincipalization A h).toAffineResolutionRule (affineSpaceEmbeddingChoice hemb hsnc hsm) =
      affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw := by
  funext k _ _ Y p _ _ _ _
  rw [EmbeddedResolutionRule.toAffineResolutionRule_apply, affineSpaceEmbeddingChoice_eq_affineSpaceEmbeddingDatum]
  exact embeddedResolutionRuleOfPrincipalization_affineSpaceEmbeddingDatum A h hemb hsnc hsm hw k Y p

end FunctorialResolution.EmbeddedResolution

end
