import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivIntegralSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivApply
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SchwInt.iteratedFDeriv_integral_eq` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIteratedFDerivIntegralSchwartz.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.iteratedFDeriv_integral_schwartz : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {P : Type} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
    (μ : Measure P) [IsFiniteMeasureOnCompacts μ]
    (G : P → SchwartzMap V ℂ), Continuous G → ∀ (C : Set P), IsCompact C → (∀ p ∉ C, G p = 0) →
    ∀ (n : ℕ) (x : V), iteratedFDeriv ℝ n (fun y => ∫ p, G p y ∂μ) x = ∫ p, iteratedFDeriv ℝ n (G p) x ∂μ := by
  first | exact @GlobalTheory.SchwInt.iteratedFDeriv_integral_eq | exact GlobalTheory.SchwInt.iteratedFDeriv_integral_eq | (intros; apply GlobalTheory.SchwInt.iteratedFDeriv_integral_eq <;> assumption)
