import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLVecMulEqLastBasis
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsGLVecMulEqLastBasis.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_GL_vecMul_eq_last_basis : ∀ {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k), ξ ≠ 0 → ∃ g : GL (Fin (n + 1)) k, Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last | exact GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last | (intros; apply GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last <;> assumption)
