import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfLocallyClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOpenOfStableUnderGeneralizationOfLocallyClosed.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_local_pieces : ∀ (X : Scheme.{0}) (Z : Set X), StableUnderGeneralization Z → (∀ x ∈ Z, ∃ (W W' : X.Opens) (J : Finset Γ(X, W')), W ≤ W' ∧ x ∈ W ∧ (∀ c ∈ J, x ∉ X.basicOpen c) ∧ ∀ y ∈ W, (∀ c ∈ J, y ∉ X.basicOpen c) → y ∈ Z) → IsOpen Z := by
  first | exact @GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces | exact GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces | (intros; apply GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces <;> assumption)
