import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PotentialCocycleDehomogenisedLaws
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPotentialCocycleDehomogenisedLaws.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.potentialCocycleDehomogenised_laws : ∀ (w N l : ℕ), 0 < N → 0 < l → (∀ F ∈ Pot ℂ w (Gam N l), cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w ∧ (∀ γ : GlobalTheory.HeckeFamilyMatrices.Lev N l, ∀ τ ∈ Hs, deh (slP ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F γ) ∧ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w → F ∈ Triv ℂ w (Gam N l))) ∧ (∀ F G, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (F + G) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F + cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) G) ∧ (∀ (c : ℂ) F, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (c • F) = c • cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  first | exact @GlobalTheory.KZ.cocP_laws | exact GlobalTheory.KZ.cocP_laws | (intros; apply GlobalTheory.KZ.cocP_laws <;> assumption)
