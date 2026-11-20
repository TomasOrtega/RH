import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockEmbeddingGLInverse
import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBlockEmbeddingGLInverse.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.block_embedding_GL_inverse : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j ≤ d → ∀ g : GL (Fin j) K, ∃ h : GL (Fin d) K,
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) ∧
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb | exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb | (intros; apply GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb <;> assumption)
