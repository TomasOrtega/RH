import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankCompletionSymmetry
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCardRankCompletionSymmetry.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.card_rank_completion_symmetry : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ), ρ ≤ n →
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm | exact GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm | (intros; apply GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm <;> assumption)
