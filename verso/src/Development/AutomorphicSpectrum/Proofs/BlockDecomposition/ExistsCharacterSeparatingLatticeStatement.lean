import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCharacterSeparatingLattice
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsCharacterSeparatingLattice.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.exists_character_separating_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A → ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne | exact GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne | (intros; apply GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne <;> assumption)
