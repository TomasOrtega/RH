import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraConjCocyclesCoboundariesPeriodSmul
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FEichlerShimuraConjCocyclesCoboundariesPeriodSmul.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.eichlerShimura_conj_cocycles_coboundaries_period_smul : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ), (∀ z ∈ Z1 Γ w, cj z ∈ Z1 Γ w) ∧ (∀ z ∈ B1 Γ w, cj z ∈ B1 Γ w) ∧ ∀ (f : ℍ → ℂ) (c : ℂ), per Γ w (c • f) = c • per Γ w f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul | exact GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul | (intros; apply GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul <;> assumption)
