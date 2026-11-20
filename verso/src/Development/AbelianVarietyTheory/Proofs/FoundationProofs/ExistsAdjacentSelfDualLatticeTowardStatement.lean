import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdjacentSelfDualLatticeToward
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinWeil.exists_adj_selfDual_step` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsAdjacentSelfDualLatticeToward.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.exists_adjacent_selfDual_lattice_toward : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → ¬ B ≤ A → ∃ A' : Submodule R X, SelfDual γ A' ∧ Adj A A' ∧ A' ≤ (A' ⊓ A) ⊔ (A' ⊓ B) := by
  first | exact @GlobalTheory.FinWeil.exists_adj_selfDual_step | exact GlobalTheory.FinWeil.exists_adj_selfDual_step | (intros; apply GlobalTheory.FinWeil.exists_adj_selfDual_step <;> assumption)
