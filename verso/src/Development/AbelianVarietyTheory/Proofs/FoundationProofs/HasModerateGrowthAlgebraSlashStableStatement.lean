import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStable
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EisM.mod_algebra` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHasModerateGrowthAlgebraSlashStable.lean&line=131#L131)
-/
theorem _root_.GlobalTheory.T.hasModerateGrowth_algebra_slash_stable : (∀ F G : ℍ → ℂ, Mod F → Mod G → Mod (fun τ => F τ + G τ) ∧ Mod (fun τ => F τ * G τ)) ∧ (∀ c : ℂ, Mod fun _ => c) ∧ (∀ (F : ℍ → ℂ) (k : ℕ) (δ : M2), 0 < δ.det → δ 1 0 = 0 → Mod F → Mod (slz k δ F)) := by
  first | exact @GlobalTheory.EisM.mod_algebra | exact GlobalTheory.EisM.mod_algebra | (intros; apply GlobalTheory.EisM.mod_algebra <;> assumption)
