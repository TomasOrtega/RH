import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformMirabolicInvari
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGeneric.colT_isMir_invariant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnipotentColumnWhittakerTransformMirabolicInvari.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.unipotentColumnWhittakerTransform_mirabolic_invariant : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, colT ψ (m + 1) f (ratGL E a γ * g) = colT ψ (m + 1) f g := by
  first | exact @GlobalTheory.CuspGeneric.colT_isMir_invariant | exact GlobalTheory.CuspGeneric.colT_isMir_invariant | (intros; apply GlobalTheory.CuspGeneric.colT_isMir_invariant <;> assumption)
