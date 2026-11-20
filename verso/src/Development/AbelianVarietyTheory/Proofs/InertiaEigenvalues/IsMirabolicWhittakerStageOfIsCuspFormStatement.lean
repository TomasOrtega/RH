import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsMirabolicWhittakerStageOfIsCuspForm.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (φ : Sm E a), IsCuspForm φ → Good ψ (a - 1) φ.1 := by
  first | exact @GlobalTheory.CuspGeneric.good_of_isCuspForm | exact GlobalTheory.CuspGeneric.good_of_isCuspForm | (intros; apply GlobalTheory.CuspGeneric.good_of_isCuspForm <;> assumption)
