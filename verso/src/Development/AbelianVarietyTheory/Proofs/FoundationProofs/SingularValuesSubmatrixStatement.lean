import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SingularValuesSubmatrix
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.singularValues_submatrix` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSingularValuesSubmatrix.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.singular_values_submatrix : ∀ (p q : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (α : ι ≃ Fin p) (β : κ ≃ Fin q) (B : Matrix (Fin p) (Fin q) ℂ), (Matrix.toEuclideanLin (B.submatrix α β) : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ι).singularValues = (Matrix.toEuclideanLin B : EuclideanSpace ℂ (Fin q) →ₗ[ℂ] EuclideanSpace ℂ (Fin p)).singularValues := by
  first | exact @GlobalTheory.singularValues_submatrix | exact GlobalTheory.singularValues_submatrix | (intros; apply GlobalTheory.singularValues_submatrix <;> assumption)
