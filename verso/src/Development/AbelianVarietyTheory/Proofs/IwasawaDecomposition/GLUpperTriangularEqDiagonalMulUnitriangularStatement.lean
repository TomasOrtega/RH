import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GLUpperTriangularEqDiagonalMulUnitriangular
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGLUpperTriangularEqDiagonalMulUnitriangular.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.GL_upperTriangular_eq_diagonal_mul_unitriangular' : ∀ (n : ℕ) (B : GL (Fin n) ℂ), B.val.BlockTriangular id → ∃ D U : GL (Fin n) ℂ, B = D * U ∧ D.val.IsDiag ∧ (∀ i, D.val i i = B.val i i) ∧ U.val.BlockTriangular id ∧ ∀ i, U.val i i = 1 := by
  first | exact @GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular | exact GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular | (intros; apply GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular <;> assumption)
