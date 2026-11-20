import Mathlib
open MeasureTheory

namespace GlobalTheory.LogDisc

open Real Set
open scoped ENNReal

/- English proof (translation)
Establish `hcont : ContinuousOn (fun s : ℝ => s ^ 2 / 2 - s * (s * Real.log s)) (Icc 0 R)` using `((by fun_prop : Continuous fun s : ℝ => s ^ 2 / 2).sub (continuous_id.mul Real.continuous_mul_log)).continuousOn`. Establish `hd : ∀ x ∈ Ioo 0 R, HasDerivWithinAt (fun s : ℝ => s ^ 2 / 2 - s * (s * Real.log s)) (-2 * (x * Real.log x)) (Ioi x) x`. Introduce `x hx`. Establish `hx0 : x ≠ 0` using `hx.1.ne'`. Establish `h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) x x`.

Simplify using `using (hasDerivAt_pow 2 x).div_const 2`. Establish `h2 : HasDerivAt (fun s : ℝ => s * (s * Real.log s)) (1 * (x * Real.log x) + x * (1 * Real.log x + x * x⁻¹)) x` using `(hasDerivAt_id' x).mul ((hasDerivAt_id' x).mul (Real.hasDerivAt_log hx0))`. Use `HasDerivAt.hasDerivWithinAt ((h1.sub h2).congr_deriv ?_)` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hR hcont hd ((continuous_const.mul Real.continuous_mul_log).intervalIntegrable 0 R)]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_neg_two_mul_mul_log {R : ℝ} (hR : 0 ≤ R) :
    ∫ s in (0:ℝ)..R, -2 * (s * Real.log s) = R ^ 2 / 2 - R ^ 2 * Real.log R := by
  have hcont : ContinuousOn (fun s : ℝ => s ^ 2 / 2 - s * (s * Real.log s)) (Icc 0 R) :=
    ((by fun_prop : Continuous fun s : ℝ => s ^ 2 / 2).sub
      (continuous_id.mul Real.continuous_mul_log)).continuousOn
  have hd : ∀ x ∈ Ioo 0 R, HasDerivWithinAt (fun s : ℝ => s ^ 2 / 2 - s * (s * Real.log s))
      (-2 * (x * Real.log x)) (Ioi x) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) x x := by
      simpa using (hasDerivAt_pow 2 x).div_const 2
    have h2 : HasDerivAt (fun s : ℝ => s * (s * Real.log s))
        (1 * (x * Real.log x) + x * (1 * Real.log x + x * x⁻¹)) x :=
      (hasDerivAt_id' x).mul ((hasDerivAt_id' x).mul (Real.hasDerivAt_log hx0))
    refine HasDerivAt.hasDerivWithinAt ((h1.sub h2).congr_deriv ?_)
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hR hcont hd
    ((continuous_const.mul Real.continuous_mul_log).intervalIntegrable 0 R)]
  simp
  ring

/- English proof (translation)
Use `set G : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (-2 * (s * Real.log s)) with hG`. Rewrite using `[← lintegral_indicator Metric.isOpen_ball.measurableSet, ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]`. Establish `h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 • (Metric.ball (0 : ℂ) R).indicator (fun x => ENNReal.ofReal (max 0 (-Real.log (‖x‖ ^ 2)))) (Complex.polarCoord.symm p) = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, (Iio R).indicator G p.1 * (fun _ : ℝ => (1 : ℝ≥0∞)) p.2`. Use `setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_` and prove the remaining obligations. Establish `hp1 : 0 < p.1` using `hp.1`.

Establish `hn : ‖Complex.polarCoord.symm p‖ = p.1`. Rewrite using `[Complex.norm_polarCoord_symm, abs_of_pos hp1]`. Distinguish the cases in `hpr : p.1 < R`. Establish `hmem : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) R`. Rewrite using `[Metric.mem_ball, dist_zero_right, hn]`.

Conclude with `hpr`. Rewrite using `[Set.indicator_of_mem hmem, Set.indicator_of_mem (show p.1 ∈ Iio R from hpr), smul_eq_mul, mul_one, ← ENNReal.ofReal_mul hp1.le, hG, hn]`. Use `congr 1`. Establish `hl : Real.log p.1 ≤ 0` using `Real.log_nonpos hp1.le (hpr.le.trans hR1)`. Rewrite using `[Real.log_pow, max_eq_right (by push_cast; linarith)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : Complex.polarCoord.symm p ∉ Metric.ball (0 : ℂ) R`. Rewrite using `[Metric.mem_ball, dist_zero_right, hn]`. Conclude with `hpr`.

Rewrite using `[Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show p.1 ∉ Iio R from hpr)]`. Simplify using the standard rewrite rules. Establish `hGm : Measurable G`. Simplify using `only [hG]`. Use `fun_prop`.

Rewrite using `[h1, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul (f := (Iio R).indicator G) (g := fun _ : ℝ => (1 : ℝ≥0∞)) (hGm.indicator measurableSet_Iio).aemeasurable (by fun_prop)]`. Rewrite using `[lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]`. Establish `hsub : Iio R ∩ Ioi (0 : ℝ) ⊆ Ioc 0 R` using `fun x hx => ⟨hx.2, hx.1.le⟩`. Establish `hint : IntegrableOn (fun s : ℝ => -2 * (s * Real.log s)) (Ioc 0 R)` using `((continuous_const.mul Real.continuous_mul_log).integrableOn_Icc (a := 0) (b := R)).mono_set Ioc_subset_Icc_self`. Establish `hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 R)] fun s : ℝ => -2 * (s * Real.log s)`.

Use `(ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => ?_)` and prove the remaining obligations. Use `Real.log_nonpos hs.1.le (hs.2.trans hR1)` as an intermediate fact. Use `hs.1` as an intermediate fact. Use `show (0:ℝ) ≤ -2 * (s * Real.log s)`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hrad : ∫⁻ s in Iio R ∩ Ioi (0 : ℝ), G s ≤ ENNReal.ofReal (R ^ 2 / 2 - R ^ 2 * Real.log R)`. Use `(lintegral_mono_set hsub).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hG, ← ofReal_integral_eq_lintegral_ofReal hint hnn, ← integral_neg_two_mul_mul_log hR0.le, intervalIntegral.integral_of_le hR0.le]`. Establish `hang : ∫⁻ _ in Ioo (-π) π, (1 : ℝ≥0∞) = ENNReal.ofReal (2 * π)`. Rewrite using `[setLIntegral_const, one_mul, Real.volume_Ioo]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hang]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_mul' (by positivity)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_ball_zero_le {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) :
    ∫⁻ x in Metric.ball (0:ℂ) R, ENNReal.ofReal (max 0 (-Real.log (‖x‖ ^ 2))) ≤
      ENNReal.ofReal (Real.pi * R ^ 2 * (1 - 2 * Real.log R)) := by
  set G : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (-2 * (s * Real.log s)) with hG
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet,
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 •
      (Metric.ball (0 : ℂ) R).indicator
        (fun x => ENNReal.ofReal (max 0 (-Real.log (‖x‖ ^ 2)))) (Complex.polarCoord.symm p) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        (Iio R).indicator G p.1 * (fun _ : ℝ => (1 : ℝ≥0∞)) p.2 := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases hpr : p.1 < R
    · have hmem : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) R := by
        rw [Metric.mem_ball, dist_zero_right, hn]; exact hpr
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show p.1 ∈ Iio R from hpr),
        smul_eq_mul, mul_one, ← ENNReal.ofReal_mul hp1.le, hG, hn]
      congr 1
      have hl : Real.log p.1 ≤ 0 := Real.log_nonpos hp1.le (hpr.le.trans hR1)
      rw [Real.log_pow, max_eq_right (by push_cast; linarith)]
      push_cast
      ring
    · have hmem : Complex.polarCoord.symm p ∉ Metric.ball (0 : ℂ) R := by
        rw [Metric.mem_ball, dist_zero_right, hn]; exact hpr
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show p.1 ∉ Iio R from hpr)]
      simp
  have hGm : Measurable G := by
    simp only [hG]
    fun_prop
  rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := (Iio R).indicator G) (g := fun _ : ℝ => (1 : ℝ≥0∞))
      (hGm.indicator measurableSet_Iio).aemeasurable (by fun_prop)]
  rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hsub : Iio R ∩ Ioi (0 : ℝ) ⊆ Ioc 0 R := fun x hx => ⟨hx.2, hx.1.le⟩
  have hint : IntegrableOn (fun s : ℝ => -2 * (s * Real.log s)) (Ioc 0 R) :=
    ((continuous_const.mul Real.continuous_mul_log).integrableOn_Icc (a := 0) (b := R)).mono_set
      Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 R)] fun s : ℝ => -2 * (s * Real.log s) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have := Real.log_nonpos hs.1.le (hs.2.trans hR1)
    have := hs.1
    show (0:ℝ) ≤ -2 * (s * Real.log s)
    nlinarith
  have hrad : ∫⁻ s in Iio R ∩ Ioi (0 : ℝ), G s ≤
      ENNReal.ofReal (R ^ 2 / 2 - R ^ 2 * Real.log R) := by
    refine (lintegral_mono_set hsub).trans (le_of_eq ?_)
    rw [hG, ← ofReal_integral_eq_lintegral_ofReal hint hnn, ← integral_neg_two_mul_mul_log hR0.le,
      intervalIntegral.integral_of_le hR0.le]
  have hang : ∫⁻ _ in Ioo (-π) π, (1 : ℝ≥0∞) = ENNReal.ofReal (2 * π) := by
    rw [setLIntegral_const, one_mul, Real.volume_Ioo]
    congr 1
    ring
  rw [hang]
  calc (∫⁻ s in Iio R ∩ Ioi (0 : ℝ), G s) * ENNReal.ofReal (2 * π)
      ≤ ENNReal.ofReal (R ^ 2 / 2 - R ^ 2 * Real.log R) * ENNReal.ofReal (2 * π) := by
        gcongr
    _ = ENNReal.ofReal (Real.pi * R ^ 2 * (1 - 2 * Real.log R)) := by
        rw [← ENNReal.ofReal_mul' (by positivity)]
        congr 1
        ring

/- English proof (translation)
Introduce `b R hR0 hR1`. Use `set f : ℂ → ℝ := fun x => max 0 (-Real.log (‖x‖ ^ 2)) with hf`. Establish `hfm : Measurable f`. Simplify using `only [hf]`. Use `fun_prop`.

Establish `hf0 : ∀ x, 0 ≤ f x` using `fun x => le_max_left _ _`. Use `set c : ℝ := -Real.log (R ^ 2) with hc`. Establish `hlogR : Real.log R ≤ 0` using `Real.log_nonpos hR0.le hR1`. Establish `hlogR2 : Real.log (R ^ 2) = 2 * Real.log R` using `by rw [Real.log_pow]; push_cast; ring`. Establish `hc0 : 0 ≤ c` using `by rw [hc, hlogR2]; linarith`.

Establish `hpt : ∀ x, ENNReal.ofReal (f x) ≤ (Metric.ball (0:ℂ) R).indicator (fun x => ENNReal.ofReal (f x)) x + ENNReal.ofReal c`. Introduce `x`. Distinguish the cases in `hx : x ∈ Metric.ball (0:ℂ) R`. Rewrite using `[indicator_of_mem hx]`. Conclude with `le_self_add`.

Rewrite using `[indicator_of_notMem hx, zero_add]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hRx : R ≤ ‖x‖` using `by simpa [Metric.mem_ball, dist_zero_right, not_lt] using hx`. Apply `max_le hc0` to reduce the goal to its premises. Rewrite using `[hc, neg_le_neg_iff]`.

Conclude with `Real.log_le_log (by positivity) (by nlinarith [norm_nonneg x])`. Establish `hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi`. Rewrite using `[← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]`. Establish `hbound : ∫⁻ x in Metric.ball b R, ENNReal.ofReal (f x) ≤ ENNReal.ofReal (Real.pi * R ^ 2 * (1 - 2 * Real.log (R ^ 2)))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[lintegral_add_right _ measurable_const, setLIntegral_const]`. Use `_ ≤ (∫⁻ x, (Metric.ball (0:ℂ) R).indicator (fun x => ENNReal.ofReal (f x)) x) + ENNReal.ofReal c * volume (Metric.ball b R) := by gcongr`. Conclude with `Measure.restrict_le_self`. Use `_ ≤ ENNReal.ofReal (Real.pi * R ^ 2 * (1 - 2 * Real.log R)) + ENNReal.ofReal (c * (Real.pi * R ^ 2)) := by`. Rewrite using `[lintegral_indicator Metric.isOpen_ball.measurableSet, Complex.volume_ball]`.

Use `gcongr`. Conclude with `lintegral_ball_zero_le hR0 hR1`. Apply `le_of_eq` to reduce the goal to its premises. Rewrite using `[hpi, ← ENNReal.ofReal_pow hR0.le, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc0]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = ENNReal.ofReal (Real.pi * R ^ 2 * (1 - 2 * Real.log (R ^ 2))) := by`. Establish `hpi0` using `Real.pi_pos`. Establish `h12 : 0 ≤ 1 - 2 * Real.log R` using `by linarith`. Rewrite using `[← ENNReal.ofReal_add (by positivity) (by positivity)]`.

Use `congr 1`. Rewrite using `[hc, hlogR2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnn : 0 ≤ᵐ[volume.restrict (Metric.ball b R)] f` using `Filter.Eventually.of_forall hf0`. Establish `hint : IntegrableOn f (Metric.ball b R)` using `⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 (hbound.trans_lt ENNReal.ofReal_lt_top)⟩`.

Use `⟨hint, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_eq_lintegral_of_nonneg_ae hnn hfm.aestronglyMeasurable]`. Use `ENNReal.toReal_le_of_le_ofReal ?_ hbound` and prove the remaining obligations. Use `Real.pi_pos` as an intermediate fact. Establish `: 0 ≤ 1 - 2 * Real.log (R ^ 2)` using `by rw [hlogR2]; linarith`.

Check the signs of the components of the expression.
-/
theorem integrableOn_and_setIntegral_posNegLogNormSq_ball_le :
    ∀ (b : ℂ) (R : ℝ), 0 < R → R ≤ 1 →
      MeasureTheory.IntegrableOn (fun x : ℂ => max 0 (-Real.log (‖x‖ ^ 2))) (Metric.ball b R) ∧
      ∫ x in Metric.ball b R, max 0 (-Real.log (‖x‖ ^ 2)) ≤
        Real.pi * R ^ 2 * (1 - 2 * Real.log (R ^ 2)) := by
  intro b R hR0 hR1
  set f : ℂ → ℝ := fun x => max 0 (-Real.log (‖x‖ ^ 2)) with hf
  have hfm : Measurable f := by
    simp only [hf]
    fun_prop
  have hf0 : ∀ x, 0 ≤ f x := fun x => le_max_left _ _
  set c : ℝ := -Real.log (R ^ 2) with hc
  have hlogR : Real.log R ≤ 0 := Real.log_nonpos hR0.le hR1
  have hlogR2 : Real.log (R ^ 2) = 2 * Real.log R := by rw [Real.log_pow]; push_cast; ring
  have hc0 : 0 ≤ c := by rw [hc, hlogR2]; linarith
  have hpt : ∀ x, ENNReal.ofReal (f x) ≤
      (Metric.ball (0:ℂ) R).indicator (fun x => ENNReal.ofReal (f x)) x + ENNReal.ofReal c := by
    intro x
    by_cases hx : x ∈ Metric.ball (0:ℂ) R
    · rw [indicator_of_mem hx]; exact le_self_add
    · rw [indicator_of_notMem hx, zero_add]
      apply ENNReal.ofReal_le_ofReal
      have hRx : R ≤ ‖x‖ := by simpa [Metric.mem_ball, dist_zero_right, not_lt] using hx
      apply max_le hc0
      rw [hc, neg_le_neg_iff]
      exact Real.log_le_log (by positivity) (by nlinarith [norm_nonneg x])
  have hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  have hbound : ∫⁻ x in Metric.ball b R, ENNReal.ofReal (f x) ≤
      ENNReal.ofReal (Real.pi * R ^ 2 * (1 - 2 * Real.log (R ^ 2))) := by
    calc ∫⁻ x in Metric.ball b R, ENNReal.ofReal (f x)
        ≤ ∫⁻ x in Metric.ball b R, ((Metric.ball (0:ℂ) R).indicator
            (fun x => ENNReal.ofReal (f x)) x + ENNReal.ofReal c) := lintegral_mono hpt
      _ = (∫⁻ x in Metric.ball b R, (Metric.ball (0:ℂ) R).indicator
            (fun x => ENNReal.ofReal (f x)) x) + ENNReal.ofReal c * volume (Metric.ball b R) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ ≤ (∫⁻ x, (Metric.ball (0:ℂ) R).indicator (fun x => ENNReal.ofReal (f x)) x) +
            ENNReal.ofReal c * volume (Metric.ball b R) := by
          gcongr
          exact Measure.restrict_le_self
      _ ≤ ENNReal.ofReal (Real.pi * R ^ 2 * (1 - 2 * Real.log R)) +
            ENNReal.ofReal (c * (Real.pi * R ^ 2)) := by
          rw [lintegral_indicator Metric.isOpen_ball.measurableSet, Complex.volume_ball]
          gcongr
          · exact lintegral_ball_zero_le hR0 hR1
          · apply le_of_eq
            rw [hpi, ← ENNReal.ofReal_pow hR0.le, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul hc0]
            congr 1
            ring
      _ = ENNReal.ofReal (Real.pi * R ^ 2 * (1 - 2 * Real.log (R ^ 2))) := by
          have hpi0 := Real.pi_pos
          have h12 : 0 ≤ 1 - 2 * Real.log R := by linarith
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hc, hlogR2]
          ring
  have hnn : 0 ≤ᵐ[volume.restrict (Metric.ball b R)] f :=
    Filter.Eventually.of_forall hf0
  have hint : IntegrableOn f (Metric.ball b R) :=
    ⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2
      (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hfm.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal ?_ hbound
  have := Real.pi_pos
  have : 0 ≤ 1 - 2 * Real.log (R ^ 2) := by rw [hlogR2]; linarith
  positivity

end GlobalTheory.LogDisc
