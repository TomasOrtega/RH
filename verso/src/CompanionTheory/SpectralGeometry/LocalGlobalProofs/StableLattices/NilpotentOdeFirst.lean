import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.OdeRoots

/- English proof (translation)
Establish `ha : 0 < s - z.re` using `sub_pos.2 hz`. Establish `h1 : inner ℝ x (z * x + y) = z.re * ‖x‖ ^ 2 + inner ℝ x y`. Rewrite using `[inner_add_right]`. Use `congr 1`. Rewrite using `[Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]`.

Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : inner ℝ x y ≤ ‖x‖ * ‖y‖` using `real_inner_le_norm x y`. Rewrite using `[h1]`. Use `set a := s - z.re with hadef`.

Use `set p := ‖x‖`. Use `set q := ‖y‖`. Establish `hs : s = a + z.re` using `by rw [hadef]; ring`. Establish `h3 : 0 ≤ (a * p - q) ^ 2 / a` using `by positivity`. Establish `h4 : (a * p - q) ^ 2 / a = a * p ^ 2 - 2 * (p * q) + (1 / a) * q ^ 2`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h5 : 2 * (z.re * p ^ 2 + inner ℝ x y) + p ^ 2 * (-2 * s) ≤ -a * p ^ 2 + (1 / a) * q ^ 2`. Rewrite using `[hs]`. Use the polynomial consequences of the given equalities and inequalities.

Use `mul_le_mul_of_nonneg_right h5 he` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem energy_pointwise (z x y : ℂ) (s e : ℝ) (hz : z.re < s) (he : 0 ≤ e) :
    2 * (inner ℝ x (z * x + y)) * e + ‖x‖ ^ 2 * (e * (-2 * s)) ≤
      -(s - z.re) * (‖x‖ ^ 2 * e) + (1 / (s - z.re)) * (‖y‖ ^ 2 * e) := by
  have ha : 0 < s - z.re := sub_pos.2 hz
  have h1 : inner ℝ x (z * x + y) = z.re * ‖x‖ ^ 2 + inner ℝ x y := by
    rw [inner_add_right]
    congr 1
    rw [Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have h2 : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  rw [h1]
  set a := s - z.re with hadef
  set p := ‖x‖
  set q := ‖y‖
  have hs : s = a + z.re := by rw [hadef]; ring
  have h3 : 0 ≤ (a * p - q) ^ 2 / a := by positivity
  have h4 : (a * p - q) ^ 2 / a = a * p ^ 2 - 2 * (p * q) + (1 / a) * q ^ 2 := by
    field_simp
    ring
  have h5 : 2 * (z.re * p ^ 2 + inner ℝ x y) + p ^ 2 * (-2 * s) ≤
      -a * p ^ 2 + (1 / a) * q ^ 2 := by
    rw [hs]
    nlinarith
  have := mul_le_mul_of_nonneg_right h5 he
  nlinarith

/- English proof (translation)
Introduce `z s hz f g hf hg hgi`. Establish `ha : 0 < s - z.re` using `sub_pos.2 hz`. Use `set a := s - z.re with hadef`. Set `ft : ℝ → ℂ` to `fun t => f (max t 0)`. Establish `hfon : ContinuousOn f (Ici 0)` using `fun t ht => (hf t ht).continuousAt.continuousWithinAt`.

Establish `hft : Continuous ft` using `hfon.comp_continuous (continuous_id.max continuous_const) (fun t => mem_Ici.2 (le_max_right _ _))`. Establish `hfe : ∀ t, 0 ≤ t → ft t = f t` using `fun t ht => by simp [ft, max_eq_left ht]`. Set `E : ℝ → ℝ` to `fun t => Real.exp (-2 * s * t)`. Establish `hE : Continuous E` using `by fun_prop`. Establish `hEpos : ∀ t, 0 ≤ E t` using `fun t => (Real.exp_pos _).le`.

Set `U : ℝ → ℝ` to `fun t => ‖ft t‖ ^ 2 * E t`. Set `V : ℝ → ℝ` to `fun t => ‖g t‖ ^ 2 * E t`. Establish `hU : Continuous U` using `by fun_prop`. Establish `hV : Continuous V` using `by fun_prop`. Establish `hUn : ∀ t, 0 ≤ U t` using `fun t => mul_nonneg (by positivity) (hEpos t)`.

Establish `hVn : ∀ t, 0 ≤ V t` using `fun t => mul_nonneg (by positivity) (hEpos t)`. Set `D : ℝ → ℝ` to `fun t => 2 * (inner ℝ (ft t) (z * ft t + g t)) * E t + ‖ft t‖ ^ 2 * (E t * (-2 * s))`. Establish `hD : Continuous D`. Establish `: Continuous fun t => inner ℝ (ft t) (z * ft t + g t)` using `Continuous.inner hft (by fun_prop)`. Use `fun_prop`.

Establish `hDle : ∀ t, D t ≤ -a * U t + (1 / a) * V t` using `fun t => energy_pointwise z (ft t) (g t) s (E t) hz (hEpos t)`. Establish `hderiv : ∀ t, 0 ≤ t → HasDerivAt (fun x => ‖f x‖ ^ 2 * E x) (D t) t`. Introduce `t ht`. Establish `h1` using `(hf t ht).norm_sq`. Establish `h2 : HasDerivAt E (E t * (-2 * s)) t`.

Use `((hasDerivAt_id t).const_mul (-2 * s)).exp` as an intermediate fact. Simplify `this` using `[E]`. Establish `e : D t = 2 * (inner ℝ (f t) (z * f t + g t)) * E t + ‖f t‖ ^ 2 * (E t * (-2 * s))`. Simplify using `only [D, hfe t ht]`. Rewrite using `[e]`.

Conclude with `h1.mul h2`. Establish `hVlin : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (V t)) < ⊤`. Use `lt_of_le_of_lt (le_of_eq ?_) hgi` and prove the remaining obligations. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Simplify using `only [V, E]`.

Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`. Establish `hVint : IntegrableOn V (Ioi 0)` using `⟨hV.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hVn)).2 hVlin⟩`. Use `set C : ℝ := ∫ t in Ioi (0 : ℝ), V t with hC`. Establish `hVle : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, V t ≤ C`. Introduce `T hT`.

Rewrite using `[intervalIntegral.integral_of_le hT]`. Conclude with `setIntegral_mono_set hVint (ae_of_all _ hVn) Ioc_subset_Ioi_self.eventuallyLE`. Establish `hbound : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, U t ≤ (U 0 + (1 / a) * C) / a`. Introduce `T hT`. Establish `hI : ∫ t in (0 : ℝ)..T, D t = ‖f T‖ ^ 2 * E T - ‖f 0‖ ^ 2 * E 0`.

Use `intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => ‖f x‖ ^ 2 * E x) (fun t ht => ?_) (hD.intervalIntegrable _ _)` and prove the remaining obligations. Rewrite `ht` using `[uIcc_of_le hT]`. Conclude with `hderiv t ht.1`. Establish `hmono : ∫ t in (0 : ℝ)..T, D t ≤ ∫ t in (0 : ℝ)..T, (-a * U t + (1 / a) * V t)` using `intervalIntegral.integral_mono_on hT (hD.intervalIntegrable _ _) (((continuous_const.mul hU).add (continuous_const.mul hV)).intervalIntegrable _ _) (fun t _ => hDle t)`. Establish `hsplit : ∫ t in (0 : ℝ)..T, (-a * U t + (1 / a) * V t) = -a * (∫ t in (0 : ℝ)..T, U t) + (1 / a) * ∫ t in (0 : ℝ)..T, V t`.

Establish `c1 : IntervalIntegrable (fun t => -a * U t) volume 0 T` using `(continuous_const.mul hU).intervalIntegrable _ _`. Establish `c2 : IntervalIntegrable (fun t => (1 / a) * V t) volume 0 T` using `(continuous_const.mul hV).intervalIntegrable _ _`. Rewrite using `[intervalIntegral.integral_add c1 c2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]`. Establish `hT0 : 0 ≤ ‖f T‖ ^ 2 * E T` using `mul_nonneg (by positivity) (hEpos T)`. Establish `hU0 : U 0 = ‖f 0‖ ^ 2 * E 0` using `by simp only [U, hfe 0 le_rfl]`.

Establish `hVa : (1 / a) * ∫ t in (0 : ℝ)..T, V t ≤ (1 / a) * C` using `mul_le_mul_of_nonneg_left (hVle T hT) (by positivity)`. Rewrite using `[le_div_iff₀ ha]`. Rewrite `hmono` using `[hI, hsplit]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hUint : IntegrableOn U (Ioi 0)`.

Use `integrableOn_Ioi_of_intervalIntegral_norm_bounded ((U 0 + (1 / a) * C) / a) 0 (l := atTop) (b := fun T : ℝ => T) (fun T => (hU.integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self) tendsto_id ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT`. Simplify `hbound T hT` using `only [Real.norm_eq_abs, abs_of_nonneg (hUn _)]`. Establish `hfin` using `hUint.lintegral_lt_top`. Use `lt_of_le_of_lt (le_of_eq ?_) hfin` and prove the remaining obligations.

Use `setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_` and prove the remaining obligations. Establish `ht0 : (0 : ℝ) ≤ t` using `le_of_lt ht`. Simplify using `only [U, E, hfe t ht0]`. Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`.
-/
theorem odeA : CompanionTheory.RgExh.Dec.N.OdeA := by
  intro z s hz f g hf hg hgi
  have ha : 0 < s - z.re := sub_pos.2 hz
  set a := s - z.re with hadef

  let ft : ℝ → ℂ := fun t => f (max t 0)
  have hfon : ContinuousOn f (Ici 0) := fun t ht =>
    (hf t ht).continuousAt.continuousWithinAt
  have hft : Continuous ft :=
    hfon.comp_continuous (continuous_id.max continuous_const) (fun t => mem_Ici.2 (le_max_right _ _))
  have hfe : ∀ t, 0 ≤ t → ft t = f t := fun t ht => by simp [ft, max_eq_left ht]
  let E : ℝ → ℝ := fun t => Real.exp (-2 * s * t)
  have hE : Continuous E := by fun_prop
  have hEpos : ∀ t, 0 ≤ E t := fun t => (Real.exp_pos _).le
  let U : ℝ → ℝ := fun t => ‖ft t‖ ^ 2 * E t
  let V : ℝ → ℝ := fun t => ‖g t‖ ^ 2 * E t
  have hU : Continuous U := by fun_prop
  have hV : Continuous V := by fun_prop
  have hUn : ∀ t, 0 ≤ U t := fun t => mul_nonneg (by positivity) (hEpos t)
  have hVn : ∀ t, 0 ≤ V t := fun t => mul_nonneg (by positivity) (hEpos t)
  let D : ℝ → ℝ := fun t =>
    2 * (inner ℝ (ft t) (z * ft t + g t)) * E t + ‖ft t‖ ^ 2 * (E t * (-2 * s))
  have hD : Continuous D := by
    have : Continuous fun t => inner ℝ (ft t) (z * ft t + g t) :=
      Continuous.inner hft (by fun_prop)
    fun_prop
  have hDle : ∀ t, D t ≤ -a * U t + (1 / a) * V t := fun t =>
    energy_pointwise z (ft t) (g t) s (E t) hz (hEpos t)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt (fun x => ‖f x‖ ^ 2 * E x) (D t) t := by
    intro t ht
    have h1 := (hf t ht).norm_sq
    have h2 : HasDerivAt E (E t * (-2 * s)) t := by
      have := ((hasDerivAt_id t).const_mul (-2 * s)).exp
      simpa [E] using this
    have e : D t = 2 * (inner ℝ (f t) (z * f t + g t)) * E t + ‖f t‖ ^ 2 * (E t * (-2 * s)) := by
      simp only [D, hfe t ht]
    rw [e]
    exact h1.mul h2

  have hVlin : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (V t)) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hgi
    refine lintegral_congr fun t => ?_
    simp only [V, E]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
  have hVint : IntegrableOn V (Ioi 0) :=
    ⟨hV.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hVn)).2 hVlin⟩
  set C : ℝ := ∫ t in Ioi (0 : ℝ), V t with hC
  have hVle : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, V t ≤ C := by
    intro T hT
    rw [intervalIntegral.integral_of_le hT]
    exact setIntegral_mono_set hVint (ae_of_all _ hVn) Ioc_subset_Ioi_self.eventuallyLE
  have hbound : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, U t ≤ (U 0 + (1 / a) * C) / a := by
    intro T hT
    have hI : ∫ t in (0 : ℝ)..T, D t = ‖f T‖ ^ 2 * E T - ‖f 0‖ ^ 2 * E 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => ‖f x‖ ^ 2 * E x) (fun t ht => ?_)
        (hD.intervalIntegrable _ _)
      rw [uIcc_of_le hT] at ht
      exact hderiv t ht.1
    have hmono : ∫ t in (0 : ℝ)..T, D t ≤ ∫ t in (0 : ℝ)..T, (-a * U t + (1 / a) * V t) :=
      intervalIntegral.integral_mono_on hT (hD.intervalIntegrable _ _)
        (((continuous_const.mul hU).add (continuous_const.mul hV)).intervalIntegrable _ _)
        (fun t _ => hDle t)
    have hsplit : ∫ t in (0 : ℝ)..T, (-a * U t + (1 / a) * V t) =
        -a * (∫ t in (0 : ℝ)..T, U t) + (1 / a) * ∫ t in (0 : ℝ)..T, V t := by
      have c1 : IntervalIntegrable (fun t => -a * U t) volume 0 T :=
        (continuous_const.mul hU).intervalIntegrable _ _
      have c2 : IntervalIntegrable (fun t => (1 / a) * V t) volume 0 T :=
        (continuous_const.mul hV).intervalIntegrable _ _
      rw [intervalIntegral.integral_add c1 c2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hT0 : 0 ≤ ‖f T‖ ^ 2 * E T := mul_nonneg (by positivity) (hEpos T)
    have hU0 : U 0 = ‖f 0‖ ^ 2 * E 0 := by simp only [U, hfe 0 le_rfl]
    have hVa : (1 / a) * ∫ t in (0 : ℝ)..T, V t ≤ (1 / a) * C :=
      mul_le_mul_of_nonneg_left (hVle T hT) (by positivity)
    rw [le_div_iff₀ ha]
    rw [hI, hsplit] at hmono
    nlinarith
  have hUint : IntegrableOn U (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      ((U 0 + (1 / a) * C) / a) 0 (l := atTop) (b := fun T : ℝ => T)
      (fun T => (hU.integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self) tendsto_id ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hUn _)] using hbound T hT
  have hfin := hUint.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  simp only [U, E, hfe t ht0]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm_eq_enorm]

end GlobalTheory.CompanionTheory.OdeRoots
