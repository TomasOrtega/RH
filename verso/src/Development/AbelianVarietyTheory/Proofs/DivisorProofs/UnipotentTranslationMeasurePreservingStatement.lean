import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTranslationMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnipotentTranslationMeasurePreserving.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.unipotent_translation_measure_preserving : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GL (Fin n) (Cinf E)), u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) → ∃ τ : Vp E n ≃ᵐ Vp E n, MeasurePreserving τ volume volume ∧ ∀ t, nu (τ t) = nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)) := by
  first | exact @GlobalTheory.WhitBump.exists_shear_measurePreserving | exact GlobalTheory.WhitBump.exists_shear_measurePreserving | (intros; apply GlobalTheory.WhitBump.exists_shear_measurePreserving <;> assumption)
