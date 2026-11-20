import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnInvMulLogSqNearZeroStatement
open MeasureTheory Filter Topology

namespace GlobalTheory.GoodTop

/- English proof (translation)
Establish `h` using `GlobalTheory.T.integrableOn_inv_mul_log_sq_near_zero`. Establish `key : Integrable (fun z : ℂ => (Set.Iic (1 / 2 : ℝ)).indicator (fun t : ℝ => (t * |Real.log t|)⁻¹ ^ 2) ‖z‖)`. Rewrite using `[integrable_fun_norm_addHaar (volume : Measure ℂ) (f := (Set.Iic (1 / 2 : ℝ)).indicator (fun t : ℝ => (t * |Real.log t|)⁻¹ ^ 2))]`. Establish `h2 : IntegrableOn ((Set.Iic (1 / 2 : ℝ)).indicator (fun t : ℝ => t * (t * |Real.log t|)⁻¹ ^ 2)) (Set.Ioi 0)`. Rewrite using `[IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn, Measure.restrict_restrict measurableSet_Iic, Set.Iic_inter_Ioi]`.

Conclude with `h`. Use `h2.congr_fun ?_ measurableSet_Ioi` and prove the remaining obligations. Introduce `t _`. Distinguish the cases in `ht : t ∈ Set.Iic (1 / 2 : ℝ)`. Simplify using `only [Set.indicator_of_mem ht, Complex.finrank_real_complex, smul_eq_mul]`.

Evaluate the numerical expressions. Simplify using `only [Set.indicator_of_notMem ht, smul_zero]`. Rewrite using `[← integrable_indicator_iff measurableSet_closedBall]`. Use `key.congr (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Distinguish the cases in `hz : ‖z‖ ∈ Set.Iic (1 / 2 : ℝ)`.

Establish `hz' : z ∈ Metric.closedBall (0 : ℂ) (1 / 2)`. Rewrite using `[mem_closedBall_zero_iff]`. Conclude with `hz`. Simplify using `only [Set.indicator_of_mem hz, Set.indicator_of_mem hz']`. Establish `hz' : z ∉ Metric.closedBall (0 : ℂ) (1 / 2)`.

Rewrite using `[mem_closedBall_zero_iff]`. Conclude with `hz`. Simplify using `only [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']`.
-/
theorem integrableOn_poincare_disc :
    IntegrableOn (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2) (Metric.closedBall 0 (1 / 2)) := by
  have h := GlobalTheory.T.integrableOn_inv_mul_log_sq_near_zero
  have key : Integrable (fun z : ℂ =>
      (Set.Iic (1 / 2 : ℝ)).indicator (fun t : ℝ => (t * |Real.log t|)⁻¹ ^ 2) ‖z‖) := by
    rw [integrable_fun_norm_addHaar (volume : Measure ℂ)
      (f := (Set.Iic (1 / 2 : ℝ)).indicator (fun t : ℝ => (t * |Real.log t|)⁻¹ ^ 2))]
    have h2 : IntegrableOn ((Set.Iic (1 / 2 : ℝ)).indicator
        (fun t : ℝ => t * (t * |Real.log t|)⁻¹ ^ 2)) (Set.Ioi 0) := by
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
        Measure.restrict_restrict measurableSet_Iic, Set.Iic_inter_Ioi]
      exact h
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro t _
    by_cases ht : t ∈ Set.Iic (1 / 2 : ℝ)
    · simp only [Set.indicator_of_mem ht, Complex.finrank_real_complex, smul_eq_mul]
      norm_num
    · simp only [Set.indicator_of_notMem ht, smul_zero]
  rw [← integrable_indicator_iff measurableSet_closedBall]
  refine key.congr (Eventually.of_forall fun z => ?_)
  by_cases hz : ‖z‖ ∈ Set.Iic (1 / 2 : ℝ)
  · have hz' : z ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
      rw [mem_closedBall_zero_iff]; exact hz
    simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hz']
  · have hz' : z ∉ Metric.closedBall (0 : ℂ) (1 / 2) := by
      rw [mem_closedBall_zero_iff]; exact hz
    simp only [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']

end GlobalTheory.GoodTop
