import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodCocycleMemCocyclesAndEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FEichlerPeriodCocycleMemCocyclesAndEq.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 2 ≤ k → ∀ f : ModularForm Γ (k : ℤ), per Γ (k - 2) ⇑f ∈ Z1 Γ (k - 2) ∧ ∀ (γ : Γ) (τ : ℍ), per Γ (k - 2) ⇑f γ = slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ)) - eichler (k - 2) ⇑f τ := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub | exact GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub | (intros; apply GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub <;> assumption)
