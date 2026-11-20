import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfSmoothOfSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGeometricallyConnectedOfSmoothOfSection.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.geometricallyConnected_of_smooth_of_section' : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ConnectedSpace X → GeometricallyConnected f := by
  first | exact @GlobalTheory.geometricallyConnected_of_smooth_of_section | exact GlobalTheory.geometricallyConnected_of_smooth_of_section | (intros; apply GlobalTheory.geometricallyConnected_of_smooth_of_section <;> assumption)
