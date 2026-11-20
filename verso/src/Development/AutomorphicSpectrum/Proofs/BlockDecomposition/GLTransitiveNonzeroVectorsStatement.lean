import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GLTransitiveNonzeroVectors
import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGLTransitiveNonzeroVectors.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.GL_transitive_nonzero_vectors : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (r r' : Fin j → K), r ≠ 0 → r' ≠ 0 →
    ∃ g : GL (Fin j) K, Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K) = r' := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows | exact GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows | (intros; apply GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows <;> assumption)
