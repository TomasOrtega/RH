import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffPeriodOneEqOfHasSum
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Hk.coef_of_hasSum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FQExpansionCoeffPeriodOneEqOfHasSum.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.qExpansionCoeffPeriodOne_eq_of_hasSum : ∀ (f : ℍ → ℂ) (a : ℕ → ℂ), (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) → ∀ n, GlobalTheory.Hk.coef f n = a n := by
  first | exact @GlobalTheory.Hk.coef_of_hasSum | exact GlobalTheory.Hk.coef_of_hasSum | (intros; apply GlobalTheory.Hk.coef_of_hasSum <;> assumption)
