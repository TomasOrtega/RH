import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainLengthBoundOfSupInf
import Mathlib

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FChainLengthBoundOfSupInf.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.chain_length_bound_of_sup_inf : ∀ {α : Type} [Lattice α] [IsModularLattice α] (C : α) (Q Q1 Q2 : α → Prop) (L1 L2 : ℕ),
    (∀ x, Q x → Q1 (x ⊓ C)) → (∀ x, Q x → Q2 (x ⊔ C)) →
    (∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q1 (N i)) → r ≤ L1) →
    (∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q2 (N i)) → r ≤ L2) →
    ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q (N i)) → r ≤ L1 + L2 := by
  first | exact @GlobalTheory.modular_chain_bound_add | exact GlobalTheory.modular_chain_bound_add | (intros; apply GlobalTheory.modular_chain_bound_add <;> assumption)
