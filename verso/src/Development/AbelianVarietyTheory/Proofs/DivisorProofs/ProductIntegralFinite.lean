import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd

open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hle : ∫⁻ z in Metric.ball (0 : Fin e → ℂ) r, ∏ k, f k (z k) ≤ ∫⁻ z : Fin e → ℂ, ∏ k, (Metric.ball (0 : ℂ) r).indicator (f k) (z k)`. Rewrite using `[← lintegral_indicator Metric.isOpen_ball.measurableSet]`. Use `lintegral_mono fun z => ?_` and prove the remaining obligations. Distinguish the cases in `hz : z ∈ Metric.ball (0 : Fin e → ℂ) r`. Rewrite using `[Set.indicator_of_mem hz]`.

Use `le_of_eq (Finset.prod_congr rfl fun k _ => ?_)` and prove the remaining obligations. Establish `hk : z k ∈ Metric.ball (0 : ℂ) r`. Rewrite `hz`, the goal using `[Metric.mem_ball, dist_zero_right]`. Conclude with `lt_of_le_of_lt (norm_le_pi_norm z k) hz`. Rewrite using `[Set.indicator_of_mem hk]`.

Rewrite using `[Set.indicator_of_notMem hz]`. Conclude with `zero_le`. Use `lt_of_le_of_lt hle ?_` and prove the remaining obligations. Rewrite using `[volume_pi, GlobalTheory.RestrMeas.lintegral_fin_prod_eq_prod (fun k => ((hf k).indicator Metric.isOpen_ball.measurableSet).aemeasurable)]`. Use `ENNReal.prod_lt_top fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[lintegral_indicator Metric.isOpen_ball.measurableSet]`. Conclude with `hfin k`.
-/
theorem setLIntegral_ball_pi_prod_lt_top {e : ℕ} (r : ℝ) (f : Fin e → ℂ → ENNReal)
    (hf : ∀ k, Measurable (f k)) (hfin : ∀ k, ∫⁻ u in Metric.ball (0 : ℂ) r, f k u < ⊤) :
    ∫⁻ z in Metric.ball (0 : Fin e → ℂ) r, ∏ k, f k (z k) < ⊤ := by
  have hle : ∫⁻ z in Metric.ball (0 : Fin e → ℂ) r, ∏ k, f k (z k) ≤
      ∫⁻ z : Fin e → ℂ, ∏ k, (Metric.ball (0 : ℂ) r).indicator (f k) (z k) := by
    rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ Metric.ball (0 : Fin e → ℂ) r
    · rw [Set.indicator_of_mem hz]
      refine le_of_eq (Finset.prod_congr rfl fun k _ => ?_)
      have hk : z k ∈ Metric.ball (0 : ℂ) r := by
        rw [Metric.mem_ball, dist_zero_right] at hz ⊢
        exact lt_of_le_of_lt (norm_le_pi_norm z k) hz
      rw [Set.indicator_of_mem hk]
    · rw [Set.indicator_of_notMem hz]
      exact zero_le
  refine lt_of_le_of_lt hle ?_
  rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fin_prod_eq_prod
    (fun k => ((hf k).indicator Metric.isOpen_ball.measurableSet).aemeasurable)]
  refine ENNReal.prod_lt_top fun k _ => ?_
  rw [lintegral_indicator Metric.isOpen_ball.measurableSet]
  exact hfin k

/- English proof (translation)
Introduce `r f hf hfin` and use `setLIntegral_ball_pi_prod_lt_top r f hf hfin`.
-/
theorem setLIntegral_ball_pi_prod_lt_top' : ∀ {e : ℕ} (r : ℝ) (f : Fin e → ℂ → ENNReal), (∀ k, Measurable (f k)) →
    (∀ k, ∫⁻ u in Metric.ball (0 : ℂ) r, f k u < ⊤) → ∫⁻ z in Metric.ball (0 : Fin e → ℂ) r, ∏ k, f k (z k) < ⊤ :=
  fun r f hf hfin => setLIntegral_ball_pi_prod_lt_top r f hf hfin

end GlobalTheory
