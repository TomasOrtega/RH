import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralEqOfBounds
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzIntegralEqOfBounds.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.schwartz_integral_eq_of_bounds : ∀ {D S : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [OpensMeasurableSpace S] (ν : Measure S) (f : S → SchwartzMap D ℂ) (F : SchwartzMap D ℂ),
    Continuous f →
    (∀ m n : ℕ, ∃ c : S → ℝ, Integrable c ν ∧ ∀ s, SchwartzMap.seminorm ℂ m n (f s) ≤ c s) →
    (∀ (n : ℕ) (x : D), iteratedFDeriv ℝ n F x = ∫ s, iteratedFDeriv ℝ n (f s) x ∂ν) →
    ∀ T : SchwartzMap D ℂ →L[ℂ] ℂ, T F = ∫ s, T (f s) ∂ν := by
  first | exact @GlobalTheory.SchwartzFormIntegral.form_integral_comm | exact GlobalTheory.SchwartzFormIntegral.form_integral_comm | (intros; apply GlobalTheory.SchwartzFormIntegral.form_integral_comm <;> assumption)
