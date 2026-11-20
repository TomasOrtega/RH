import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Smoothness supplies an étale chart on an open neighbourhood of x. Use the assignment that selects no coordinate at any index. The empty list has no valid indices, so the distinctness and both ideal conditions hold vacuously.
-/
theorem inStrictNormalCrossingPositionAt_nil {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    InStrictNormalCrossingPositionAt p ([] : List X.IdealSheafData) x := by
  obtain ⟨U, m, hxU, _, hc⟩ := exists_etaleChart p x
  obtain ⟨c⟩ := hc
  refine ⟨U, hxU, m, c, fun _ => none, ?_, ?_, ?_⟩
  · intro i hi
    simp at hi
  · intro i hi
    simp at hi
  · intro i hi
    simp at hi

/- English proof (authored)
There are no divisors in the list to check for smoothness. At each point the preceding local result supplies the required étale chart for the empty list.
-/
theorem inStrictNormalCrossingPosition_nil {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] :
    InStrictNormalCrossingPosition p ([] : List X.IdealSheafData) := by
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, fun x => inStrictNormalCrossingPositionAt_nil p x⟩
  intro D hD
  simp at hD

end FunctorialResolution.EmbeddedResolution
