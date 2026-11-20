import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtCharSeriesCoefZero
import Mathlib

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.continuousAt_charSeries_coef_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContinuousAtCharSeriesCoefZero.lean&line=178#L178)
-/
theorem _root_.GlobalTheory.T.continuousAt_coeff_zero_of_continuousAt_char_series : ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 := by
  first | exact @GlobalTheory.continuousAt_charSeries_coef_zero | exact GlobalTheory.continuousAt_charSeries_coef_zero | (intros; apply GlobalTheory.continuousAt_charSeries_coef_zero <;> assumption)
