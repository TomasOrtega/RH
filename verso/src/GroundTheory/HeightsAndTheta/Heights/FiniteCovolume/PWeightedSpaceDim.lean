import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField NumberField.InfinitePlace Module

/- English proof (translation)
Unfold `WeightedSpaceDim.Statement`. Rewrite using `[finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, IsTotallyComplex.finrank]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem WeightedSpaceDim.proof (E : Type*) [Field E] [NumberField E] [IsTotallyComplex E] :
    WeightedSpaceDim.Statement E := by
  unfold WeightedSpaceDim.Statement
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin,
    card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
    IsTotallyComplex.finrank]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
