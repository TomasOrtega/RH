import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankEichlerShimuraCoboundariesOfGammaLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FFinrankEichlerShimuraCoboundariesOfGammaLe.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.finrank_b1_eq_of_gamma_le : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ), 0 < M → 1 ≤ w → CongruenceSubgroup.Gamma M ≤ Γ → Module.finrank ℂ (B1 Γ w) = w + 1 := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le | exact GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le <;> assumption)
