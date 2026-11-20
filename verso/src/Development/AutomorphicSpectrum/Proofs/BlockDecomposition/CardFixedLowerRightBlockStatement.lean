import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFixedLowerRightBlock
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCardFixedLowerRightBlock.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.card_fixed_lower_right_block : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (D : Matrix (Fin n) (Fin n) k),
    Nat.card {g : GL (Ix n) k // dBlk g = D} =
      Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} *
        Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CntHalf.card_lowerRightBlock_eq_fibre_formula | exact GlobalTheory.CompanionTheory.Jp.CntHalf.card_lowerRightBlock_eq_fibre_formula | (intros; apply GlobalTheory.CompanionTheory.Jp.CntHalf.card_lowerRightBlock_eq_fibre_formula <;> assumption)
