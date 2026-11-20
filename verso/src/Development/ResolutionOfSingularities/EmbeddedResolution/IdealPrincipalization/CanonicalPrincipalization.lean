import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
A blowup along an ideal sheaf on a Noetherian scheme is Noetherian by the blowup theorem for Noetherian schemes. Apply that theorem to the stated witness of the blowup property.
-/
theorem blowupPreservesNoetherian : BlowupPreservesNoetherian.{u} := by
  repeat intro _
  rename_i h
  exact isNoetherian_of_isBlowupAlongIdealSheaf h

def canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) : PrincipalizationRules.{u} where
  divisorRed := fun T alg j =>
    DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T alg j
  maxOrderRed := fun T rc => orderReductionSeq comapIsoInvariance T rc
  orderRed := fun T rc => MaxContactReduction.reduceOrder comapIsoInvariance T rc

def canonicalPrincipalization (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hrad : SmoothSubschemeIdealIsRadical.{u}) : PrincipalizationAlgorithm.{u} :=
  (canonicalAlgorithmRules hres).principalization hrad

/- English proof (authored)
The canonical principalization is the principalization constructed from the canonical reduction rules. Those rules satisfy dimension reduction and commute with the specified closed immersions by hypothesis, and smooth center ideals satisfy the required radical condition. The functoriality theorem for principalization from such rules gives the claim.
-/
theorem isFunctorialPrincipalization_canonicalPrincipalization (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical.{u})
    (hemb : CommutesWithClosedImmersion.{u} (canonicalAlgorithmRules hres)) :
    IsFunctorialPrincipalization (canonicalPrincipalization hres hrad) :=
  PrincipalizationRules.isFunctorialPrincipalization_principalization (canonicalAlgorithmRules hres) hB hrad hemb

end FunctorialResolution.EmbeddedResolution

end
