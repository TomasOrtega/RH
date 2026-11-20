import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentAdaptedToDecreasingChainA
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLinearIndependentAdaptedToDecreasingChainA.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.exists_linearIndependent_adapted_to_decreasing_chain' : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ), (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) → (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ), LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧ ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by
  first | exact @GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain | exact GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain | (intros; apply GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain <;> assumption)
