import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralContinuousMultilinearMapPiMeasure
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIntegralContinuousMultilinearMapPiMeasure.lean&line=128#L128)
-/
theorem _root_.GlobalTheory.T.integral_continuousMultilinearMap_pi_measure : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (E : ι → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)] (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i), (∀ i, Integrable (g i) (μ i)) → Integrable (fun x : ∀ i, X i => Φ fun i => g i (x i)) (Measure.pi μ) ∧ ∫ x, Φ (fun i => g i (x i)) ∂Measure.pi μ = Φ fun i => ∫ y, g i y ∂μ i := by
  first | exact @GlobalTheory.MultilinFubini.integral_multilinear_pi | exact GlobalTheory.MultilinFubini.integral_multilinear_pi | (intros; apply GlobalTheory.MultilinFubini.integral_multilinear_pi <;> assumption)
