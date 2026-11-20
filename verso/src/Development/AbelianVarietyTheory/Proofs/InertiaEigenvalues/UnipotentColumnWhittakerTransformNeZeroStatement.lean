import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGeneric.colT_ne_zero_of_good` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnipotentColumnWhittakerTransformNeZero.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.unipotentColumnWhittakerTransform_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → f ≠ 0 → colT ψ (m + 1) f ≠ 0 := by
  first | exact @GlobalTheory.CuspGeneric.colT_ne_zero_of_good | exact GlobalTheory.CuspGeneric.colT_ne_zero_of_good | (intros; apply GlobalTheory.CuspGeneric.colT_ne_zero_of_good <;> assumption)
