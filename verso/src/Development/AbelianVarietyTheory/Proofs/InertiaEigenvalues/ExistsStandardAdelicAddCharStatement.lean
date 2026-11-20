import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGeneric.exists_stdPsi` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsStandardAdelicAddChar.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.exists_standardAdelicAddChar : ∀ (E : Type) [Field E] [NumberField E], ∃ ψ : AddChar (Ad E) ℂ, StdPsi ψ := by
  first | exact @GlobalTheory.CuspGeneric.exists_stdPsi | exact GlobalTheory.CuspGeneric.exists_stdPsi | (intros; apply GlobalTheory.CuspGeneric.exists_stdPsi <;> assumption)
