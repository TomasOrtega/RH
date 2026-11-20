import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseOfFibrewiseInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsLeftInverseOfFibrewiseInjective.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.exists_left_inverse_of_fibrewise_injective : ∀ (R : Type) [CommRing R] (m n : ℕ) (Q : Matrix (Fin m) (Fin n) R), (∀ (K : Type) [Field K] (φ : R →+* K), Function.Injective (Q.map φ).mulVec) → ∃ Q' : Matrix (Fin n) (Fin m) R, Q' * Q = 1 := by
  first | exact @GlobalTheory.matrix_exists_left_inverse_of_forall_field | exact GlobalTheory.matrix_exists_left_inverse_of_forall_field | (intros; apply GlobalTheory.matrix_exists_left_inverse_of_forall_field <;> assumption)
