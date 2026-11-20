import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

noncomputable def logCutoff (k : ℕ) (z : ℂ) : ℝ :=
  if z = 0 then 0 else Real.smoothTransition (2 + Real.log ‖z‖ / ((k : ℝ) + 1))

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
/- English proof (translation)
Unfold `_root_.GlobalTheory.GoodTop.logCutoff`. Use `split_ifs with h0`. Both sides reduce to the same expression. Apply `Real.smoothTransition.zero_of_nonpos` to reduce the goal to its premises. Establish `hk : (0 : ℝ) < (k : ℝ) + 1` using `by positivity`.

Establish `hlog : Real.log ‖z‖ ≤ -2 * ((k : ℝ) + 1)`. Rewrite using `[← Real.log_exp (-2 * ((k : ℝ) + 1))]`. Conclude with `Real.log_le_log (norm_pos_iff.mpr h0) hz`. Rewrite using `[← sub_nonneg, show 0 - (2 + Real.log ‖z‖ / ((k : ℝ) + 1)) = (-2 * ((k : ℝ) + 1) - Real.log ‖z‖) / ((k : ℝ) + 1) by field_simp; ring]`. Conclude with `div_nonneg (by linarith) hk.le`.
-/
private lemma logCutoff_eq_zero_of_norm_le (k : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ Real.exp (-2 * ((k : ℝ) + 1))) : _root_.GlobalTheory.GoodTop.logCutoff k z = 0 := by
  unfold _root_.GlobalTheory.GoodTop.logCutoff
  split_ifs with h0
  · rfl
  apply Real.smoothTransition.zero_of_nonpos
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlog : Real.log ‖z‖ ≤ -2 * ((k : ℝ) + 1) := by
    rw [← Real.log_exp (-2 * ((k : ℝ) + 1))]
    exact Real.log_le_log (norm_pos_iff.mpr h0) hz
  rw [← sub_nonneg, show 0 - (2 + Real.log ‖z‖ / ((k : ℝ) + 1)) =
    (-2 * ((k : ℝ) + 1) - Real.log ‖z‖) / ((k : ℝ) + 1) by field_simp; ring]
  exact div_nonneg (by linarith) hk.le

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
/- English proof (translation)
Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `z`. Distinguish the cases in `h0 : z = 0`. Substitute `h0` using the available equality. Establish `hev : _root_.GlobalTheory.GoodTop.logCutoff k =ᶠ[𝓝 0] fun _ => 0` using `by filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-2 * ((k : ℝ) + 1)))] with w hw`.

Rewrite `hw` using `[Metric.mem_ball, dist_zero_right]`. Conclude with `logCutoff_eq_zero_of_norm_le k hw.le`. Conclude with `contDiffAt_const.congr_of_eventuallyEq hev`. Establish `hev : _root_.GlobalTheory.GoodTop.logCutoff k =ᶠ[𝓝 z] fun w => Real.smoothTransition (2 + Real.log ‖w‖ / ((k : ℝ) + 1))` using `by filter_upwards [isOpen_ne.mem_nhds h0] with w hw`. Simplify using `only [_root_.GlobalTheory.GoodTop.logCutoff, if_neg (show w ≠ 0 from hw)]`.

Use `ContDiffAt.congr_of_eventuallyEq ?_ hev` and prove the remaining obligations. Use `Real.smoothTransition.contDiff.contDiffAt.comp z ?_` and prove the remaining obligations. Use `contDiffAt_const.add (ContDiffAt.div_const ?_ _)` and prove the remaining obligations. Conclude with `(Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr h0)).comp z (contDiffAt_norm ℝ h0)`.
-/
lemma _root_.GlobalTheory.GoodTop.contDiff_logCutoff (k : ℕ) : ContDiff ℝ ∞ (_root_.GlobalTheory.GoodTop.logCutoff k) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases h0 : z = 0
  · subst h0
    have hev : _root_.GlobalTheory.GoodTop.logCutoff k =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-2 * ((k : ℝ) + 1)))] with w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      exact logCutoff_eq_zero_of_norm_le k hw.le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hev : _root_.GlobalTheory.GoodTop.logCutoff k =ᶠ[𝓝 z]
        fun w => Real.smoothTransition (2 + Real.log ‖w‖ / ((k : ℝ) + 1)) := by
      filter_upwards [isOpen_ne.mem_nhds h0] with w hw
      simp only [_root_.GlobalTheory.GoodTop.logCutoff, if_neg (show w ≠ 0 from hw)]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    refine Real.smoothTransition.contDiff.contDiffAt.comp z ?_
    refine contDiffAt_const.add (ContDiffAt.div_const ?_ _)
    exact (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr h0)).comp z (contDiffAt_norm ℝ h0)

end GlobalTheory.GoodTop
