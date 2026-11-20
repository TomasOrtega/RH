import Mathlib

noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Filter Topology

open Set

/- English proof (translation)
Establish `: (fun p : ℝ × ℝ => Complex.polarCoord.symm p) = fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I)`. Use function extensionality and compare the values at `p`. Simplify using `[Complex.polarCoord_symm_apply]`. Rewrite using `[this]`. Use `fun_prop`.
-/
theorem pgds_cont_polar_symm : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  have : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
      fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
    funext p; simp [Complex.polarCoord_symm_apply]
  rw [this]; fun_prop

/- English proof (translation)
Establish `hc` using `pgds_cont_polar_symm`. Establish `hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p)) (Icc 0 r ×ˢ Icc (-Real.pi) Real.pi)`. Apply `ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)` to reduce the goal to its premises. Apply `ContinuousOn.mul (continuous_fst.continuousOn)` to reduce the goal to its premises. Use `hF.comp hc.continuousOn ?_` and prove the remaining obligations.

Introduce `p hp`. Simplify using `only [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm]`. Rewrite using `[abs_of_nonneg hp.1.1]`. Conclude with `hp.1.2`. Establish `hint'` using `hint.mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)`.

Use `⟨hint', ?_⟩` and prove the remaining obligations. Establish `hpre : MeasurableSet ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r)` using `hc.measurable Metric.isOpen_ball.measurableSet`. Rewrite using `[← integral_indicator Metric.isOpen_ball.measurableSet, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]`. Establish `h1 : (fun p : ℝ × ℝ => p.1 • (Metric.ball (0:ℂ) r).indicator F (Complex.polarCoord.symm p)) = ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r).indicator (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p))`. Use function extensionality and compare the values at `p`.

Distinguish the cases in `hp : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) r`. Rewrite using `[indicator_of_mem hp, indicator_of_mem (show p ∈ _ from hp), smul_eq_mul]`. Rewrite using `[indicator_of_notMem hp, indicator_of_notMem (show p ∉ _ from hp), smul_zero]`. Rewrite using `[h1, setIntegral_indicator hpre]`. Establish `h2 : Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi ∩ ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r) = Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi`.

Use extensionality with `p`. Simplify using `only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo, mem_preimage, Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h0, hθ⟩, hr⟩`. Rewrite `hr` using `[abs_of_pos h0]`.

Conclude with `⟨⟨h0, hr⟩, hθ⟩`. Introduce and unpack `⟨⟨h0, hr⟩, hθ⟩`. Use `⟨⟨h0, hθ⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[abs_of_pos h0]`. Conclude with `hr`.

Rewrite using `[h2, Measure.volume_eq_prod]`. Rewrite `hint'` using `[Measure.volume_eq_prod]`. Conclude with `setIntegral_prod _ hint'`.
-/
theorem pgds_integral_ball_polar {r : ℝ} (F : ℂ → ℝ) (hF : ContinuousOn F (Metric.closedBall 0 r)) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p))
        (Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi) ∧
    ∫ z in Metric.ball (0 : ℂ) r, F z =
      ∫ s in Ioo 0 r, ∫ θ in Ioo (-Real.pi) Real.pi, s * F (Complex.polarCoord.symm (s, θ)) := by
  have hc := pgds_cont_polar_symm
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p))
      (Icc 0 r ×ˢ Icc (-Real.pi) Real.pi) := by
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    apply ContinuousOn.mul (continuous_fst.continuousOn)
    refine hF.comp hc.continuousOn ?_
    intro p hp
    simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm]
    rw [abs_of_nonneg hp.1.1]; exact hp.1.2
  have hint' := hint.mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  refine ⟨hint', ?_⟩
  have hpre : MeasurableSet ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r) :=
    hc.measurable Metric.isOpen_ball.measurableSet
  rw [← integral_indicator Metric.isOpen_ball.measurableSet, ← Complex.integral_comp_polarCoord_symm,
    polarCoord_target]
  have h1 : (fun p : ℝ × ℝ => p.1 • (Metric.ball (0:ℂ) r).indicator F (Complex.polarCoord.symm p)) =
      ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r).indicator
        (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p)) := by
    funext p
    by_cases hp : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) r
    · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ _ from hp), smul_eq_mul]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ _ from hp), smul_zero]
  rw [h1, setIntegral_indicator hpre]
  have h2 : Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi ∩
      ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r) =
      Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo, mem_preimage, Metric.mem_ball,
      dist_zero_right, Complex.norm_polarCoord_symm]
    constructor
    · rintro ⟨⟨h0, hθ⟩, hr⟩; rw [abs_of_pos h0] at hr; exact ⟨⟨h0, hr⟩, hθ⟩
    · rintro ⟨⟨h0, hr⟩, hθ⟩; refine ⟨⟨h0, hθ⟩, ?_⟩; rw [abs_of_pos h0]; exact hr
  rw [h2, Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod] at hint'
  exact setIntegral_prod _ hint'

def discI (a R : ℝ) : ℝ :=
  ∫ z in Metric.ball (0 : ℂ) R, Real.exp (-(a * ‖z‖ ^ 2))

/- English proof (translation)
Unfold `discI`. Rewrite using `[(pgds_integral_ball_polar (r := R) (fun z : ℂ => Real.exp (-(a * ‖z‖ ^ 2))) (by fun_prop)).2, intervalIntegral.integral_of_le hR, integral_Ioc_eq_integral_Ioo]`. Use `setIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)` and prove the remaining obligations. Simplify using `only [Complex.norm_polarCoord_symm]`. Rewrite using `[abs_of_pos hs.1, setIntegral_const]`.

Simplify using `only [measureReal_def, Real.volume_Ioo, smul_eq_mul]`. Rewrite using `[ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pgds_discI_eq (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    discI a R = ∫ s in (0:ℝ)..R, 2 * Real.pi * (s * Real.exp (-(a * s ^ 2))) := by
  unfold discI
  rw [(pgds_integral_ball_polar (r := R) (fun z : ℂ => Real.exp (-(a * ‖z‖ ^ 2)))
    (by fun_prop)).2, intervalIntegral.integral_of_le hR, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
  simp only [Complex.norm_polarCoord_symm]
  rw [abs_of_pos hs.1, setIntegral_const]
  simp only [measureReal_def, Real.volume_Ioo, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/- English proof (translation)
Rewrite using `[pgds_discI_eq a hR]`. Establish `hd : ∀ x ∈ uIcc 0 R, HasDerivAt (fun s => -(Real.pi / a) * Real.exp (-(a * s ^ 2))) (2 * Real.pi * (x * Real.exp (-(a * x ^ 2)))) x`. Introduce `x _`. Use `(((hasDerivAt_pow 2 x).const_mul a).neg.exp).const_mul (-(Real.pi / a))` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations.

Rewrite using `[show (2:ℕ) - 1 = 1 from rfl, pow_one]`. Simplify using `only [Pi.neg_apply, Nat.cast_ofNat]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]`. Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, neg_zero, Real.exp_zero, mul_one]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem discI_of_pos {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    discI a R = Real.pi * (1 - Real.exp (-(a * R ^ 2))) / a := by
  rw [pgds_discI_eq a hR]
  have hd : ∀ x ∈ uIcc 0 R, HasDerivAt (fun s => -(Real.pi / a) * Real.exp (-(a * s ^ 2)))
      (2 * Real.pi * (x * Real.exp (-(a * x ^ 2)))) x := by
    intro x _
    have := (((hasDerivAt_pow 2 x).const_mul a).neg.exp).const_mul (-(Real.pi / a))
    refine this.congr_deriv ?_
    rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
    simp only [Pi.neg_apply, Nat.cast_ofNat]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, neg_zero,
    Real.exp_zero, mul_one]
  ring

/- English proof (translation)
Rewrite using `[pgds_discI_eq 0 hR]`. Simplify using `only [zero_mul, neg_zero, Real.exp_zero, mul_one]`. Rewrite using `[intervalIntegral.integral_const_mul, integral_id]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem discI_zero {R : ℝ} (hR : 0 ≤ R) : discI 0 R = Real.pi * R ^ 2 := by
  rw [pgds_discI_eq 0 hR]
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/- English proof (translation)
Break down `ha.lt_or_eq with ha | ha` into its components or cases. Rewrite using `[discI_of_pos ha hR.le]`. Establish `: Real.exp (-(a * R ^ 2)) < 1` using `Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hR])`. Use `Real.pi_pos` as an intermediate fact. Apply `div_pos _ ha` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Substitute `ha` using the available equality. Rewrite using `[discI_zero hR.le]`. Use `Real.pi_pos` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem discI_pos {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) : 0 < discI a R := by
  rcases ha.lt_or_eq with ha | ha
  · rw [discI_of_pos ha hR.le]
    have : Real.exp (-(a * R ^ 2)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hR])
    have := Real.pi_pos
    apply div_pos _ ha
    nlinarith
  · subst ha; rw [discI_zero hR.le]; have := Real.pi_pos; positivity

/- English proof (translation)
Establish `hs : (R / Real.sqrt t) ^ 2 = R ^ 2 / t`. Rewrite using `[div_pow, Real.sq_sqrt ht.le]`. Establish `hR' : 0 ≤ R / Real.sqrt t` using `div_nonneg hR (Real.sqrt_nonneg t)`. Break down `ha.lt_or_eq with ha | ha` into its components or cases. Rewrite using `[discI_of_pos (mul_pos ht ha) hR', discI_of_pos ha hR, hs]`.

Establish `: t * a * (R ^ 2 / t) = a * R ^ 2` using `by field_simp`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Substitute `ha` using the available equality. Rewrite using `[mul_zero, discI_zero hR', discI_zero hR, hs]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem discI_scale {a R t : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) (ht : 0 < t) :
    discI (t * a) (R / Real.sqrt t) = discI a R / t := by
  have hs : (R / Real.sqrt t) ^ 2 = R ^ 2 / t := by
    rw [div_pow, Real.sq_sqrt ht.le]
  have hR' : 0 ≤ R / Real.sqrt t := div_nonneg hR (Real.sqrt_nonneg t)
  rcases ha.lt_or_eq with ha | ha
  · rw [discI_of_pos (mul_pos ht ha) hR', discI_of_pos ha hR, hs]
    have : t * a * (R ^ 2 / t) = a * R ^ 2 := by field_simp
    rw [this]
    field_simp
  · subst ha; rw [mul_zero, discI_zero hR', discI_zero hR, hs]; ring

/- English proof (translation)
Establish `hpi` using `Real.pi_pos`. Use `set h : ℂ → ℂ := fun z => g z ^ 2 with hh`. Establish `habs : |s| = s` using `abs_of_pos hs`. Establish `hdiff : DiffContOnCl ℂ h (Metric.ball 0 |s|)`. Apply `DifferentiableOn.diffContOnCl` to reduce the goal to its premises.

Rewrite using `[closure_ball _ (by rw [habs]; exact hs.ne'), habs]`. Conclude with `(hg.pow 2).mono (Metric.closedBall_subset_ball hsR)`. Establish `hav` using `hdiff.circleAverage`. Rewrite `hav` using `[Real.circleAverage_def]`. Establish `hper : Function.Periodic (fun θ => ‖h (circleMap 0 s θ)‖) (2 * Real.pi)`.

Introduce `θ`. Simplify using `only`. Rewrite using `[periodic_circleMap 0 s θ]`. Establish `e1` using `hper.intervalIntegral_add_eq 0 (-Real.pi)`. Rewrite `e1` using `[zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring]`.

Establish `hle : ‖h 0‖ ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖h (circleMap 0 s θ)‖`. Rewrite using `[← hav, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]`. Use `gcongr`. Conclude with `intervalIntegral.norm_integral_le_integral_norm (by positivity)`. Rewrite `hle` using `[e1, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]`.

Establish `hcm : ∀ θ : ℝ, circleMap 0 s θ = Complex.polarCoord.symm (s, θ)`. Introduce `θ`. Simplify using `[circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]`. Simplify using `only [hcm, hh, norm_pow] at hle`. Rewrite `hle` using `[inv_mul_eq_div, le_div_iff₀ (by positivity)]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pgds_circle {R s : ℝ} (hs : 0 < s) (hsR : s < R) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R)) :
    2 * Real.pi * ‖g 0‖ ^ 2 ≤
      ∫ θ in Ioo (-Real.pi) Real.pi, ‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 := by
  have hpi := Real.pi_pos
  set h : ℂ → ℂ := fun z => g z ^ 2 with hh
  have habs : |s| = s := abs_of_pos hs
  have hdiff : DiffContOnCl ℂ h (Metric.ball 0 |s|) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by rw [habs]; exact hs.ne'), habs]
    exact (hg.pow 2).mono (Metric.closedBall_subset_ball hsR)
  have hav := hdiff.circleAverage
  rw [Real.circleAverage_def] at hav
  have hper : Function.Periodic (fun θ => ‖h (circleMap 0 s θ)‖) (2 * Real.pi) := by
    intro θ; simp only; rw [periodic_circleMap 0 s θ]
  have e1 := hper.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at e1
  have hle : ‖h 0‖ ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖h (circleMap 0 s θ)‖ := by
    rw [← hav, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    gcongr
    exact intervalIntegral.norm_integral_le_integral_norm (by positivity)
  rw [e1, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo] at hle
  have hcm : ∀ θ : ℝ, circleMap 0 s θ = Complex.polarCoord.symm (s, θ) := by
    intro θ
    simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  simp only [hcm, hh, norm_pow] at hle
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)] at hle
  linarith

/- English proof (translation)
Establish `hgc : ContinuousOn g (Metric.closedBall 0 r)` using `hg.continuousOn.mono (Metric.closedBall_subset_ball hrR)`. Take `⟨hiR, eR⟩` from `pgds_integral_ball_polar (r := r) (fun z => ‖g z‖ ^ 2 * w ‖z‖) ((hgc.norm.pow 2).mul (hwc.comp continuous_norm).continuousOn)`. Take `⟨-, eL⟩` from `pgds_integral_ball_polar (r := r) (fun z => w ‖z‖) (hwc.comp continuous_norm).continuousOn`. Rewrite using `[eL, eR, ← integral_const_mul]`. Establish `hI : Integrable (fun p : ℝ × ℝ => p.1 * (‖g (Complex.polarCoord.symm p)‖ ^ 2 * w ‖Complex.polarCoord.symm p‖)) ((volume.restrict (Ioo 0 r)).prod (volume.restrict (Ioo (-Real.pi) Real.pi)))`.

Rewrite using `[Measure.prod_restrict, ← Measure.volume_eq_prod]`. Conclude with `hiR`. Use `integral_mono_of_nonneg ?_ hI.integral_prod_left ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs`. Conclude with `mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioo fun θ _ => mul_nonneg hs.1.le (hw _))`.

Use `filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs`. Establish `key` using `pgds_circle hs.1 (hs.2.trans hrR) g hg`. Simplify using `only [Complex.norm_polarCoord_symm, abs_of_pos hs.1]`. Rewrite using `[setIntegral_const]`. Simplify using `only [measureReal_def, Real.volume_Ioo, smul_eq_mul]`.

Rewrite using `[ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]`. Establish `e : ∀ θ : ℝ, s * (‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 * w s) = (s * w s) * ‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2` using `fun θ => by ring`. Simplify using `only [e]`. Rewrite using `[integral_const_mul]`. Establish `hsw : 0 ≤ s * w s` using `mul_nonneg hs.1.le (hw s)`.

Use `mul_le_mul_of_nonneg_left key hsw` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem disc_mean_le {R r : ℝ} (hr : 0 < r) (hrR : r < R) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R)) (w : ℝ → ℝ) (hwc : Continuous w)
    (hw : ∀ s, 0 ≤ w s) :
    ‖g 0‖ ^ 2 * ∫ z in Metric.ball (0 : ℂ) r, w ‖z‖ ≤
      ∫ z in Metric.ball (0 : ℂ) r, ‖g z‖ ^ 2 * w ‖z‖ := by
  have hgc : ContinuousOn g (Metric.closedBall 0 r) :=
    hg.continuousOn.mono (Metric.closedBall_subset_ball hrR)
  obtain ⟨hiR, eR⟩ := pgds_integral_ball_polar (r := r) (fun z => ‖g z‖ ^ 2 * w ‖z‖)
    ((hgc.norm.pow 2).mul (hwc.comp continuous_norm).continuousOn)
  obtain ⟨-, eL⟩ := pgds_integral_ball_polar (r := r) (fun z => w ‖z‖)
    (hwc.comp continuous_norm).continuousOn
  rw [eL, eR, ← integral_const_mul]
  have hI : Integrable (fun p : ℝ × ℝ => p.1 * (‖g (Complex.polarCoord.symm p)‖ ^ 2 *
      w ‖Complex.polarCoord.symm p‖))
      ((volume.restrict (Ioo 0 r)).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hiR
  refine integral_mono_of_nonneg ?_ hI.integral_prod_left ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioo
      fun θ _ => mul_nonneg hs.1.le (hw _))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have key := pgds_circle hs.1 (hs.2.trans hrR) g hg
    simp only [Complex.norm_polarCoord_symm, abs_of_pos hs.1]
    rw [setIntegral_const]
    simp only [measureReal_def, Real.volume_Ioo, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    have e : ∀ θ : ℝ, s * (‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 * w s) =
        (s * w s) * ‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 := fun θ => by ring
    simp only [e]
    rw [integral_const_mul]
    have hsw : 0 ≤ s * w s := mul_nonneg hs.1.le (hw s)
    have := mul_le_mul_of_nonneg_left key hsw
    nlinarith

end ReciprocityTheory.GeometryOfNumbersTheory
