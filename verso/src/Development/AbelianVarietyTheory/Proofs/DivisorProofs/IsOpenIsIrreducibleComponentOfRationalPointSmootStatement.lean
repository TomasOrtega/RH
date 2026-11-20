import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIsIrreducibleComponentOfRationalPointSmoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOpenIsIrreducibleComponentOfRationalPointSmoot.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧ IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field | exact GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field | (intros; apply GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field <;> assumption)
