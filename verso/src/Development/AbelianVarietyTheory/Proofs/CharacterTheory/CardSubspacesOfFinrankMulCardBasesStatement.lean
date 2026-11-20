import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardSubspacesOfFinrankMulCardBases
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FCardSubspacesOfFinrankMulCardBases.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.card_subspaces_of_finrank_mul_card_bases : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V → Nat.card {W : Submodule F V // Module.finrank F W = a} * ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) = ∏ i ∈ Finset.range a, (Nat.card F ^ Module.finrank F V - Nat.card F ^ i) := by
  first | exact @GlobalTheory.SubspaceNumber.card_subspaces_mul | exact GlobalTheory.SubspaceNumber.card_subspaces_mul | (intros; apply GlobalTheory.SubspaceNumber.card_subspaces_mul <;> assumption)
