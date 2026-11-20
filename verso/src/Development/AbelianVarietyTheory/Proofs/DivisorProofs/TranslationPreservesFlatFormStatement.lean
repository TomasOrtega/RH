import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationPreservesFlatForm
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TranslFlat.transl_holomorphic_preserves_flat_form` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTranslationPreservesFlatForm.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.translation_preserves_flat_form : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ x : Fl g, DifferentiableOn ℂ (transl τ x) (cov B g) ∧ ∀ P ∈ cov B g, pull (transl τ x) (om0 τ) P = om0 τ P := by
  first | exact @GlobalTheory.TranslFlat.transl_holomorphic_preserves_flat_form | exact GlobalTheory.TranslFlat.transl_holomorphic_preserves_flat_form | (intros; apply GlobalTheory.TranslFlat.transl_holomorphic_preserves_flat_form <;> assumption)
