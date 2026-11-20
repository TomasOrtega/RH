import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif

open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CntSwap

def swapW (k : Type) [Field k] (n : ℕ) : GL (Ix n) k :=
  ⟨fromBlocks 0 1 1 0, fromBlocks 0 1 1 0,
    by simp [fromBlocks_multiply, fromBlocks_one],
    by simp [fromBlocks_multiply, fromBlocks_one]⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma lowerRightBlock_mul_block_swap {k : Type} [Field k] {n : ℕ} (g : GL (Ix n) k) :
    dBlk (g * swapW k n) = lowerLeftBlock g := by
  show (g.1 * fromBlocks 0 1 1 0).toBlocks₂₂ = g.1.toBlocks₂₁
  conv_lhs => rw [← fromBlocks_toBlocks g.1]
  rw [fromBlocks_multiply]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_lower_left_rank_eq_card_lower_right_rank : ∀ (k : Type) [Field k] [Fintype k] (n i : ℕ),
    Nat.card {g : GL (Ix n) k // (lowerLeftBlock g).rank = i} = Nat.card {g : GL (Ix n) k // (dBlk g).rank = i} := by
  intro k _ _ n i
  exact Nat.card_congr ((Equiv.mulRight (swapW k n)).subtypeEquiv (fun g => by
    rw [Equiv.coe_mulRight, lowerRightBlock_mul_block_swap]))

end GlobalTheory.CompanionTheory.Jp.CntSwap
