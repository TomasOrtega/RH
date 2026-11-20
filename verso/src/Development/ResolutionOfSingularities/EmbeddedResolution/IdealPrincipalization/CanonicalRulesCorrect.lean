import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.CanonicalDivisorReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometricPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MaxOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderReductionCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The dimension reduction specification requires a divisor reduction, invariance of that reduction under the stated change of boundary position, and the two order reduction specifications. The divisor reduction hypotheses give the first two properties for the canonical divisor rule. The geometric hypotheses give the maximal-order reduction property for any supplied lower-dimensional procedure satisfying its specification. The strict-transform blowup hypothesis gives the ordinary order reduction property. Together these establish the specification of the rules.
-/
theorem isCorrect_canonicalAlgorithmRules_of_hypotheses
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hdiv : DivisorReduction.DivisorReductionHypotheses hres)
    (hG : PrincipalizationGeometryHypotheses.{u}) :
    (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension where
  divisorSpec := isBoundaryDivisorReduction_divisorFamily_canonicalAlgorithmRules hres hdiv
  divisorShift := isBoundaryPositionInvariant_divisorFamily_canonicalAlgorithmRules hres hdiv
  maxOrderSpec := fun n A L hspec =>
    MaxOrderReduction.isMaxOrderReduction_canonicalAlgorithmRules hG hres n A L hspec
  orderSpec := OrderReductionProperties.isOrderReduction_orderFamily_of_strictTransformIsBlowup hres

/- English proof (authored)
The canonical divisor rules satisfy the divisor reduction hypotheses, and the geometric principalization results supply the general geometric hypotheses. Insert these two results into the conditional correctness theorem for the canonical rules.
-/
theorem isCorrect_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension :=
  isCorrect_canonicalAlgorithmRules_of_hypotheses hres
    (divisorReductionHypotheses_canonicalAlgorithmRules hres)
    principalizationGeometryHypotheses.{u}

end FunctorialResolution.EmbeddedResolution
