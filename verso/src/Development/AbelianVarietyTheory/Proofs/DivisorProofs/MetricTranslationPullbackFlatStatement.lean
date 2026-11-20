import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricTranslationPullbackFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationPreservesFlatFormStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMetricTranslationPullbackFlat.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.metric_translation_pullback_flat : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ), IsMetric B τ M j h → ChernIsFlat B τ h → ∀ x : Fl g, IsMetric B τ M (translPullFactor τ x j) (fun P => h (transl τ x P)) ∧ ChernIsFlat B τ (fun P => h (transl τ x P)) := by
  first | exact @GlobalTheory.FlatTransl.translate_isMetric_chernIsFlat | exact GlobalTheory.FlatTransl.translate_isMetric_chernIsFlat | (intros; apply GlobalTheory.FlatTransl.translate_isMetric_chernIsFlat <;> assumption)
