import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIsotypicFactorOfIsIrreduciblePiFiniteGroups.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.isotypic_factor_of_isIrreducible_pi_finite_groups : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (∀ i, G i) W), ρ.IsIrreducible → ∀ i, ∃ (n : ℕ) (τ : Representation ℂ (G i) (Fin n → ℂ)), τ.IsIrreducible ∧ (∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, Function.Injective φ ∧ ∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ Submodule.span ℂ {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} = ⊤ := by
  first | exact @GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi | exact GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi | (intros; apply GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi <;> assumption)
