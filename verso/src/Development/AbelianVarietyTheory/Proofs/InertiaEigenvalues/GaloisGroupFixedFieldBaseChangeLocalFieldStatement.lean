import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Ram.baseChange_fixedField` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGaloisGroupFixedFieldBaseChangeLocalField.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.galoisGroup_fixedField_baseChange_localField : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (A : Subgroup (L ≃ₐ[K] L)), ∃ j : (L ≃ₐ[↥(IntermediateField.fixedField A)] L) →* (L ≃ₐ[K] L), Function.Injective j ∧ j.range = A ∧ (∀ σ x, j σ x = σ x) ∧ ∀ i : ℤ, lowerRamificationGroup ↥(IntermediateField.fixedField A) L i = (lowerRamificationGroup K L i).comap j := by
  first | exact @GlobalTheory.PMon.Ram.baseChange_fixedField | exact GlobalTheory.PMon.Ram.baseChange_fixedField | (intros; apply GlobalTheory.PMon.Ram.baseChange_fixedField <;> assumption)
