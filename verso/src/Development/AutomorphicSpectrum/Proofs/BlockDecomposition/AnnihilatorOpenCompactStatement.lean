import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorOpenCompact
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAnnihilatorOpenCompact.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.annihilator_open_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ∧ IsCompact {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact | exact GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact | (intros; apply GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact <;> assumption)
