import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableUnderGeneralizationSectionComponents
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.stableUnderGeneralization_sectionComponents` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStableUnderGeneralizationSectionComponents.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.stableUnderGeneralization_section_connectedComponentIn : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → StableUnderGeneralization {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.stableUnderGeneralization_sectionComponents | exact GlobalTheory.stableUnderGeneralization_sectionComponents | (intros; apply GlobalTheory.stableUnderGeneralization_sectionComponents <;> assumption)
