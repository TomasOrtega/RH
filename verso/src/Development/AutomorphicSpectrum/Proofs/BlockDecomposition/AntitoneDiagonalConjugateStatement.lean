import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AntitoneDiagonalConjugate
import Mathlib
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAntitoneDiagonalConjugate.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.antitone_diagonal_conjugate : ∀ {n : ℕ} (U₀ : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U₀ ∈ Matrix.unitaryGroup (Fin n) ℂ → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧ U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ = U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ ∧ ∀ Z : Matrix (Fin n) (Fin n) ℂ, (U₀ᴴ * Z * U₀).IsDiag → (Uᴴ * Z * U).IsDiag := by
  first | exact @GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder | exact GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder | (intros; apply GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder <;> assumption)
