import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.CovLog
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCutHess
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHessCCompPluri
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogLogCutHessDeriv
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogLogCutHessConst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

/- English proof (translation)
Unfold `tubeWeight`. Apply the tactic sequence `split_ifs <;> positivity`.
-/
theorem tubeWeight_nonneg {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) : 0 ≤ tubeWeight Q y := by
  unfold tubeWeight
  split_ifs <;> positivity

/- English proof (translation)
Take `⟨K, hK0, hK⟩` from `logLogStep_deriv2_bound`. Use `⟨K, hK0, fun m Q k y => ?_⟩` and prove the remaining obligations. Establish `hc : (1 : ℝ) ≤ (k : ℝ) + 1` using `by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]`. Establish `hnn : 0 ≤ K / ((k : ℝ) + 1) * tubeWeight Q y` using `mul_nonneg (div_nonneg hK0 (by linarith)) (tubeWeight_nonneg Q y)`. Establish `hconst : ∀ c : ℝ, logLogCut Q k =ᶠ[𝓝 y] (fun _ => c) → ∃ a b : ℝ, |a| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧ |b| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧ hessC (logLogCut Q k) y = (a : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y ∧ hessC (fun z => logLogCut Q k z ^ 2 / 2) y = (b : …`.

Introduce `c hev`. Take `⟨e1, e2⟩` from `hessC_of_eventually_const hev`. Conclude with `⟨0, 0, by simpa using hnn, by simpa using hnn, by simp [e1], by simp [e2]⟩`. Distinguish the cases in `h1 : ‖eval y Q‖ ^ 2 < cutLevel k`. Conclude with `hconst 0 (logLogCut_eventually_zero Q k h1)`.

Distinguish the cases in `h2 : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval y Q‖ ^ 2`. Conclude with `hconst 1 (logLogCut_eventually_one Q k h2)`. Establish `hw0 : 0 < ‖eval y Q‖ ^ 2` using `lt_of_lt_of_le (cutLevel_mem k).1 (not_lt.1 h1)`. Establish `hw1 : ‖eval y Q‖ ^ 2 < 1` using `lt_of_le_of_lt (not_lt.1 h2) (Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _)))`. Establish `hLy : logAbsSq Q y ≤ -1`.

Establish `e1 : logAbsSq Q y ≤ -Real.exp (((k : ℝ) + 1) / 2)` using `(Real.log_le_iff_le_exp hw0).2 (not_lt.1 h2)`. Establish `e2 : 1 ≤ Real.exp (((k : ℝ) + 1) / 2)` using `Real.one_le_exp (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `htw : tubeWeight Q y = (logAbsSq Q y ^ 2)⁻¹` using `if_pos hLy`. Establish `hg : AnalyticAt ℂ (fun z => eval z Q) y` using `AnalyticOnNhd.eval_mvPolynomial Q y (Set.mem_univ y)`.

Establish `hgy : eval y Q ≠ 0`. Introduce `h`. Rewrite `hw0` using `[h, norm_zero]`. Evaluate the numerical expressions using `at hw0`. Establish `hLcd : ContDiffAt ℝ 2 (logAbsSq Q) y` using `(((contDiff_norm_sq ℝ).contDiffAt).comp y (hg.contDiffAt.restrict_scalars ℝ)).log hw0.ne'`.

Establish `hlcd : ContDiffAt ℝ 2 (fun z => Real.log ‖eval z Q‖) y` using `((contDiffAt_norm ℝ hgy).comp y (hg.contDiffAt.restrict_scalars ℝ)).log (norm_ne_zero_iff.2 hgy)`. Establish `hLpl : hessC (logAbsSq Q) y = 0`. Establish `e : logAbsSq Q = fun z => Real.log ‖eval z Q‖ + Real.log ‖eval z Q‖`. Use function extensionality and compare the values at `z`. Rewrite using `[logAbsSq, Real.log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(hessC_add_log_norm _ (fun z => eval z Q) y hlcd hg hgy).trans (hessC_log_norm _ y hg hgy)`. Take `⟨hFcd, hHcd, hF2, hH2⟩` from `hK ((k : ℝ) + 1) hc (logAbsSq Q y) (by linarith)`.

Establish `hev` using `logLogCut_eventually_step Q k hw0 hw1`. Establish `hevsq : (fun z => logLogCut Q k z ^ 2 / 2) =ᶠ[𝓝 y] fun z => cutStep (Real.log (-logAbsSq Q z) / ((k : ℝ) + 1)) ^ 2 / 2` using `by filter_upwards [hev] with z hz`. Rewrite using `[hz]`. Establish `eF` using `hC m (fun x => cutStep (Real.log (-x) / ((k : ℝ) + 1))) (logAbsSq Q) y hFcd hLcd hLpl`. Establish `eH` using `hC m (fun x => cutStep (Real.log (-x) / ((k : ℝ) + 1)) ^ 2 / 2) (logAbsSq Q) y hHcd hLcd hLpl`.

Rewrite `eF` using `[← hessC_congr' hev]`. Rewrite `eH` using `[← hessC_congr' hevsq]`. Use `⟨_, _, ?_, ?_, eF, eH⟩` and prove the remaining obligations. Rewrite using `[htw, ← div_eq_mul_inv, div_div]`. Conclude with `hF2`.

Rewrite using `[htw, ← div_eq_mul_inv, div_div]`. Conclude with `hH2`.
-/
theorem LogLogCutHess.proof (hC : HessCCompPluri.Statement) : LogLogCutHess.Statement := by
  obtain ⟨K, hK0, hK⟩ := logLogStep_deriv2_bound
  refine ⟨K, hK0, fun m Q k y => ?_⟩
  have hc : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hnn : 0 ≤ K / ((k : ℝ) + 1) * tubeWeight Q y :=
    mul_nonneg (div_nonneg hK0 (by linarith)) (tubeWeight_nonneg Q y)
  have hconst : ∀ c : ℝ, logLogCut Q k =ᶠ[𝓝 y] (fun _ => c) → ∃ a b : ℝ,
      |a| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧ |b| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧
      hessC (logLogCut Q k) y = (a : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y ∧
      hessC (fun z => logLogCut Q k z ^ 2 / 2) y = (b : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y := by
    intro c hev
    obtain ⟨e1, e2⟩ := hessC_of_eventually_const hev
    exact ⟨0, 0, by simpa using hnn, by simpa using hnn, by simp [e1], by simp [e2]⟩
  by_cases h1 : ‖eval y Q‖ ^ 2 < cutLevel k
  · exact hconst 0 (logLogCut_eventually_zero Q k h1)
  by_cases h2 : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval y Q‖ ^ 2
  · exact hconst 1 (logLogCut_eventually_one Q k h2)
  have hw0 : 0 < ‖eval y Q‖ ^ 2 := lt_of_lt_of_le (cutLevel_mem k).1 (not_lt.1 h1)
  have hw1 : ‖eval y Q‖ ^ 2 < 1 :=
    lt_of_le_of_lt (not_lt.1 h2) (Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _)))
  have hLy : logAbsSq Q y ≤ -1 := by
    have e1 : logAbsSq Q y ≤ -Real.exp (((k : ℝ) + 1) / 2) := (Real.log_le_iff_le_exp hw0).2 (not_lt.1 h2)
    have e2 : 1 ≤ Real.exp (((k : ℝ) + 1) / 2) := Real.one_le_exp (by positivity)
    linarith
  have htw : tubeWeight Q y = (logAbsSq Q y ^ 2)⁻¹ := if_pos hLy
  have hg : AnalyticAt ℂ (fun z => eval z Q) y := AnalyticOnNhd.eval_mvPolynomial Q y (Set.mem_univ y)
  have hgy : eval y Q ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw0
    norm_num at hw0
  have hLcd : ContDiffAt ℝ 2 (logAbsSq Q) y :=
    (((contDiff_norm_sq ℝ).contDiffAt).comp y (hg.contDiffAt.restrict_scalars ℝ)).log hw0.ne'
  have hlcd : ContDiffAt ℝ 2 (fun z => Real.log ‖eval z Q‖) y :=
    ((contDiffAt_norm ℝ hgy).comp y (hg.contDiffAt.restrict_scalars ℝ)).log (norm_ne_zero_iff.2 hgy)
  have hLpl : hessC (logAbsSq Q) y = 0 := by
    have e : logAbsSq Q = fun z => Real.log ‖eval z Q‖ + Real.log ‖eval z Q‖ := by
      funext z
      rw [logAbsSq, Real.log_pow]
      push_cast
      ring
    rw [e]
    exact (hessC_add_log_norm _ (fun z => eval z Q) y hlcd hg hgy).trans (hessC_log_norm _ y hg hgy)
  obtain ⟨hFcd, hHcd, hF2, hH2⟩ := hK ((k : ℝ) + 1) hc (logAbsSq Q y) (by linarith)
  have hev := logLogCut_eventually_step Q k hw0 hw1
  have hevsq : (fun z => logLogCut Q k z ^ 2 / 2) =ᶠ[𝓝 y]
      fun z => cutStep (Real.log (-logAbsSq Q z) / ((k : ℝ) + 1)) ^ 2 / 2 := by
    filter_upwards [hev] with z hz
    rw [hz]
  have eF := hC m (fun x => cutStep (Real.log (-x) / ((k : ℝ) + 1))) (logAbsSq Q) y hFcd hLcd hLpl
  have eH := hC m (fun x => cutStep (Real.log (-x) / ((k : ℝ) + 1)) ^ 2 / 2) (logAbsSq Q) y hHcd hLcd hLpl
  rw [← hessC_congr' hev] at eF
  rw [← hessC_congr' hevsq] at eH
  refine ⟨_, _, ?_, ?_, eF, eH⟩
  · rw [htw, ← div_eq_mul_inv, div_div]; exact hF2
  · rw [htw, ← div_eq_mul_inv, div_div]; exact hH2

end

end GroundTheory.Heights₂.Heights
