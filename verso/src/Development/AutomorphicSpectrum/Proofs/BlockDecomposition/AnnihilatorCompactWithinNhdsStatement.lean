import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorCompactWithinNhds
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAnnihilatorCompactWithinNhds.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.annihilator_compact_within_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (S : Set (Fin n → k)), S ∈ nhds (0 : Fin n → k) → ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧ ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset | exact GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset | (intros; apply GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset <;> assumption)
