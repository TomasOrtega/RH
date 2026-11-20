import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactCoverData

/- English proof (translation)
Establish `hc` using `(isMaxContactCover_chosenCoverData T hv h).covers`. Rewrite using `[coverMap_eq_sigmaOpensDesc]`. Conclude with `surjective_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens hc`.
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
