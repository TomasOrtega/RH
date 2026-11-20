import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMatrixCoefficientsMem
import Mathlib

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CommRepBlocks.coeff_mem_of_blocks` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnipotentMatrixCoefficientsMem.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.unipotent_matrix_coefficients_mem : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] (H : Set G) (S : Submodule ℂ (G → ℂ)), (∀ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (χ : G → ℂ), (∀ s, IsNilpotent (ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ))) → (∀ γ ∈ H, ρ γ = 1) → (∀ i j, Continuous fun s => ρ s i j) → ∀ i j, (fun s => ρ s i j) ∈ S) → ∀ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ), (∀ γ ∈ H, ρ γ = 1) → (∀ i j, Continuous fun s => ρ s i j) → ∀ i j, (fun s => ρ s i j) ∈ S := by
  first | exact @GlobalTheory.CommRepBlocks.coeff_mem_of_blocks | exact GlobalTheory.CommRepBlocks.coeff_mem_of_blocks | (intros; apply GlobalTheory.CommRepBlocks.coeff_mem_of_blocks <;> assumption)
