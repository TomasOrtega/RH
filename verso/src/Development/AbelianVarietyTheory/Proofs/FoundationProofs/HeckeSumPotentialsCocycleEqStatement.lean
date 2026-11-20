import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumPotentialsCocycleEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.DictHk.dict_hk` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHeckeSumPotentialsCocycleEq.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.heckeSum_potentials_cocycle_eq : ∀ (N l w : ℕ) (α : Matrix (Fin 2) (Fin 2) ℤ) (ι : Type) [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < N → 0 < l → 0 < α.det → GlobalTheory.HeckeFamilyMatrices.IsDCReps (GlobalTheory.HeckeFamilyMatrices.Lev N l) α δ → ∀ F ∈ Pot ℂ w (Gam N l), (∑ i, opP ℂ (δ i) F) ∈ Pot ℂ w (Gam N l) ∧ cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (∑ i, opP ℂ (δ i) F) = GlobalTheory.HeckeFamilyMatrices.hk (GlobalTheory.HeckeFamilyMatrices.Lev N l) w δ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  first | exact @GlobalTheory.KZ.DictHk.dict_hk | exact GlobalTheory.KZ.DictHk.dict_hk | (intros; apply GlobalTheory.KZ.DictHk.dict_hk <;> assumption)
