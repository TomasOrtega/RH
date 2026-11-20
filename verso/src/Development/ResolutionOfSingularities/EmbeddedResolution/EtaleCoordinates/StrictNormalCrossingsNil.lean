import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Take `⟨U, m, hxU, _, hc⟩` from `exists_etaleChart p x`. Take `⟨c⟩` from `hc`. Use `⟨U, hxU, m, c, fun _ => none, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Simplify using `at hi`.

Introduce `i hi`. Simplify using `at hi`. Introduce `i hi`. Simplify using `at hi`.
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

/- English proof (translation)
Rewrite using `[inStrictNormalCrossingPosition_iff]`. Use `⟨?_, fun x => inStrictNormalCrossingPositionAt_nil p x⟩` and prove the remaining obligations. Introduce `D hD`. Simplify using `at hD`.
-/
theorem inStrictNormalCrossingPosition_nil {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] :
    InStrictNormalCrossingPosition p ([] : List X.IdealSheafData) := by
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, fun x => inStrictNormalCrossingPositionAt_nil p x⟩
  intro D hD
  simp at hD

end FunctorialResolution.EmbeddedResolution
