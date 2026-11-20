import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LogGapMeasurableScaleStable
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FLogGapMeasurableScaleStable.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.log_gap_measurable_scale_stable : ∀ (n : ℕ) (h : HermNorm n) (u : Fin n → ℂ),
  Measurable (logGap h u) ∧ ∀ s : ℝ≥0∞, IsOpen {y | s < logGap h u y} ∧ IsScaleStable {y | s < logGap h u y} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic <;> assumption)
