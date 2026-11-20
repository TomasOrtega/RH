import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterAnnihilatorIntegerLattice
open ValuativeRel MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCharacterAnnihilatorIntegerLattice.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.character_annihilator_integer_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (b : k), b ≠ 0 → IsCompact {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} ∧ IsOpen {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator | exact GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator | (intros; apply GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator <;> assumption)
