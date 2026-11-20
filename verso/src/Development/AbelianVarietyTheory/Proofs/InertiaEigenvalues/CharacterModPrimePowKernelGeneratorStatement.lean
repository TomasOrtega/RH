import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterModPrimePowKernelGenerator
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Ram.character_kernel_generator` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCharacterModPrimePowKernelGenerator.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.character_mod_prime_pow_kernel_generator : ∀ (G : Type) [Group G] (p r : ℕ) (a : G → ℤ), p.Prime → (∀ σ τ, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ) → (∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) → ∃ (J : Subgroup G) (_ : J.Normal) (σ₁ : G) (c : ℤ), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧ c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ ∧ ¬ (p : ℤ) ∣ c := by
  first | exact @GlobalTheory.PMon.Ram.character_kernel_generator | exact GlobalTheory.PMon.Ram.character_kernel_generator | (intros; apply GlobalTheory.PMon.Ram.character_kernel_generator <;> assumption)
