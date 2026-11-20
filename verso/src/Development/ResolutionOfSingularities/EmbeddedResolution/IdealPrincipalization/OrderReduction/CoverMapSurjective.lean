import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactCoverData

/- English proof (authored)
The chosen maximal-contact opens cover the original scheme. The cover map is induced by their inclusions from the disjoint union of the opens. Each point belongs to one of those opens and is the image of its copy in that summand, so the map is surjective.
-/
theorem surjective_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (h : ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
      MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T)) :
    Surjective (coverMap T hv) := by
  have hc := (isMaxContactCover_chosenCoverData T hv h).covers
  rw [coverMap_eq_sigmaOpensDesc]
  exact surjective_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens hc

end MaxContactCoverData

end FunctorialResolution.EmbeddedResolution
