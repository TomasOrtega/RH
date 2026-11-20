import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianContainingIsotropicRat
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsLagrangianContainingIsotropicRat.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_lagrangian_containing_isotropic_rat' : ∀ (g r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (I : Submodule ℚ (Fin r → ℚ)), r = 2 * g → Mqᵀ = -Mq → Mq.det ≠ 0 → (∀ x ∈ I, ∀ y ∈ I, x ⬝ᵥ Mq *ᵥ y = 0) → ∃ L : Submodule ℚ (Fin r → ℚ), I ≤ L ∧ (∀ x ∈ L, ∀ y ∈ L, x ⬝ᵥ Mq *ᵥ y = 0) ∧ Module.finrank ℚ L = g := by
  first | exact @GlobalTheory.exists_lagrangian_containing_isotropic_rat | exact GlobalTheory.exists_lagrangian_containing_isotropic_rat | (intros; apply GlobalTheory.exists_lagrangian_containing_isotropic_rat <;> assumption)
