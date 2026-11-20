import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeToNumberField
open scoped TensorProduct Polynomial
/- English proof (citation)
Apply `GlobalTheory.exists_numberField_point_ne_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteTypeToNumberField.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.finite_type_to_number_field : ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A → ∀ a : A, a ≠ 0 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (χ : A →+* K), χ a ≠ 0 := by
  first | exact @_root_.GlobalTheory.exists_numberField_point_ne_zero | exact _root_.GlobalTheory.exists_numberField_point_ne_zero | (intros; apply _root_.GlobalTheory.exists_numberField_point_ne_zero <;> assumption)
