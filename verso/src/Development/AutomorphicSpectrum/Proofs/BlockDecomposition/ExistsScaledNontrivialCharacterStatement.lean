import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScaledNontrivialCharacter
open ValuativeRel MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsScaledNontrivialCharacter.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_scaled_nontrivial_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (a c : k), valuation k a < 1 → ψ c ≠ 1 → ∃ d : k, ψ d ≠ 1 ∧ (∃ r : ℕ, ∃ μ ∈ 𝒪[k], d = μ * a ^ r * c) ∧ ∀ s ∈ 𝒪[k], ψ (s * a * d) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step | exact GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step | (intros; apply GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step <;> assumption)
