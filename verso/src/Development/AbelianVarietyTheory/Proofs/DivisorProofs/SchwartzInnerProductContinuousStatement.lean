import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInnerProductContinuous
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.schwartz_pairing_conj_clm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzInnerProductContinuous.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.schwartz_inner_product_continuous : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (w : SchwartzMap V ℂ), ∃ Λ : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      Λ u = @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (w x)) := by
  first | exact @GlobalTheory.schwartz_pairing_conj_clm | exact GlobalTheory.schwartz_pairing_conj_clm | (intros; apply GlobalTheory.schwartz_pairing_conj_clm <;> assumption)
