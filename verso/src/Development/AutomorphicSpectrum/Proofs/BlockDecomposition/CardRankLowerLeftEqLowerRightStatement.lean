import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankLowerLeftEqLowerRight
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCardRankLowerLeftEqLowerRight.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.card_rank_lower_left_eq_lower_right : ∀ (k : Type) [Field k] [Fintype k] (n i : ℕ),
    Nat.card {g : GL (Ix n) k // (lowerLeftBlock g).rank = i} = Nat.card {g : GL (Ix n) k // (dBlk g).rank = i} := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank | exact GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank | (intros; apply GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank <;> assumption)
