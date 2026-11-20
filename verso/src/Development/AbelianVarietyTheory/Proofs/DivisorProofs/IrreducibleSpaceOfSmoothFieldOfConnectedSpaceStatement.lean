import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIrreducibleSpaceOfSmoothFieldOfConnectedSpace.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.irreducibleSpace_of_smooth_over_field_of_connected : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)), Smooth f → ConnectedSpace X → IrreducibleSpace X := by
  first | exact @GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace | exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace | (intros; apply GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace <;> assumption)
