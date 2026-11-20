import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormL2Bound
import Mathlib

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzSeminormL2Bound.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.schwartz_seminorm_l2_bound : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
        C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by
  first | exact @GlobalTheory.schwartz_pow_mul_iteratedFDeriv_le_sqrt_sum_weighted_sq | exact GlobalTheory.schwartz_pow_mul_iteratedFDeriv_le_sqrt_sum_weighted_sq | (intros; apply GlobalTheory.schwartz_pow_mul_iteratedFDeriv_le_sqrt_sum_weighted_sq <;> assumption)
