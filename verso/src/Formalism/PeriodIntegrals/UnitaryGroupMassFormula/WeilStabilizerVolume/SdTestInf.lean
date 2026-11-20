import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.SdUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensInfAll
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RealCharacter

noncomputable section

namespace PI.VolStabW

namespace SdTestInfW

open MeasureTheory Complex Filter Topology

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.UnitaryCharacterOfReals.char_real f hc hadd hn`.
-/
theorem char_real (f : ℝ → ℂ) (hc : Continuous f) (hadd : ∀ s t, f (s + t) = f s * f t)
    (hn : ∀ s, ‖f s‖ = 1) : ∃ b : ℝ, ∀ s : ℝ, f s = exp (↑(b * s) * I) :=
  _root_.UpperTheory.Reformulated.B.UnitaryCharacterOfReals.char_real f hc hadd hn

/- English proof (translation)
Assume the negation of the conclusion as `huv`. Establish `hne : u - v ≠ 0` using `sub_ne_zero.2 huv`. Establish `h1` using `h (Real.pi / (u - v))`. Establish `h2 : exp (↑((u - v) * (Real.pi / (u - v))) * I) = 1`. Establish `: (↑((u - v) * (Real.pi / (u - v))) : ℂ) * I = ↑(u * (Real.pi / (u - v))) * I - ↑(v * (Real.pi / (u - v))) * I` using `by push_cast; ring`.

Rewrite using `[this, Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]`. Rewrite `h2` using `[mul_div_cancel₀ _ hne, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions using `at h2`.
-/
theorem freq_unique {u v : ℝ} (h : ∀ s : ℝ, exp (↑(u * s) * I) = exp (↑(v * s) * I)) : u = v := by
  by_contra huv
  have hne : u - v ≠ 0 := sub_ne_zero.2 huv
  have h1 := h (Real.pi / (u - v))
  have h2 : exp (↑((u - v) * (Real.pi / (u - v))) * I) = 1 := by
    have : (↑((u - v) * (Real.pi / (u - v))) : ℂ) * I =
        ↑(u * (Real.pi / (u - v))) * I - ↑(v * (Real.pi / (u - v))) * I := by
      push_cast; ring
    rw [this, Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  rw [mul_div_cancel₀ _ hne, Complex.exp_pi_mul_I] at h2
  norm_num at h2

section Bichar

open scoped RealInnerProductSpace

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

structure IsBichar (χ : W → W → ℂ) : Prop where
  addL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y
  addR : ∀ x y y', χ x (y + y') = χ x y * χ x y'
  norm1 : ∀ x y, ‖χ x y‖ = 1
  contL : ∀ y, Continuous fun x => χ x y
  contR : ∀ x, Continuous (χ x)

/- English proof (translation)
Establish `hne : χ 0 y ≠ 0` using `fun h0 => by have := h.norm1 0 y; rw [h0, norm_zero] at this; exact zero_ne_one this`. Establish `e` using `h.addL 0 0 y`. Rewrite `e` using `[add_zero]`. Conclude with `mul_left_cancel₀ hne (by rw [mul_one]; exact e.symm)`.
-/
theorem IsBichar.zero_left {χ : W → W → ℂ} (h : IsBichar χ) (y : W) : χ 0 y = 1 := by
  have hne : χ 0 y ≠ 0 := fun h0 => by have := h.norm1 0 y; rw [h0, norm_zero] at this; exact zero_ne_one this
  have e := h.addL 0 0 y
  rw [add_zero] at e
  exact mul_left_cancel₀ hne (by rw [mul_one]; exact e.symm)

/- English proof (translation)
The claim follows from `char_real (fun s => χ (s • v) y) ((h.contL y).comp (continuous_id.smul continuous_const)) (fun s t => by simp only [add_smul]; exact h.addL _ _ y) (fun s => h.norm1 _ y)`.
-/
theorem IsBichar.freq {χ : W → W → ℂ} (h : IsBichar χ) (v y : W) :
    ∃ β : ℝ, ∀ s : ℝ, χ (s • v) y = exp (↑(β * s) * I) :=
  char_real (fun s => χ (s • v) y) ((h.contL y).comp (continuous_id.smul continuous_const))
    (fun s t => by simp only [add_smul]; exact h.addL _ _ y) (fun s => h.norm1 _ y)

/- English proof (translation)
Rewrite using `[arg_exp_mul_I, toIocMod_eq_self]`. Conclude with `⟨h.1, by linarith [h.2, Real.pi_pos]⟩`.
-/
theorem arg_exp_small {θ : ℝ} (h : θ ∈ Set.Ioo (-Real.pi) Real.pi) : arg (exp (↑θ * I)) = θ := by
  rw [arg_exp_mul_I, toIocMod_eq_self]
  exact ⟨h.1, by linarith [h.2, Real.pi_pos]⟩

/- English proof (translation)
Set `g : ℕ → W → ℝ` to `fun m y => ((m : ℝ) + 1) * arg (χ ((1 / ((m : ℝ) + 1)) • v) y)`. Establish `hg : ∀ m, Measurable (g m)` using `fun m => measurable_const.mul (measurable_arg.comp (h.contR _).measurable)`. Use `measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.2 fun y => ?_)` and prove the remaining obligations. Establish `ht : Tendsto (fun m : ℕ => β y * (1 / ((m : ℝ) + 1))) atTop (𝓝 (β y * 0))` using `(tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (β y)`. Rewrite `ht` using `[mul_zero]`.

Establish `hev` using `ht (Ioo_mem_nhds (neg_lt_zero.2 Real.pi_pos) Real.pi_pos)`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [hev] with m hm`. Simplify using `only [g]`. Rewrite using `[hβ y, arg_exp_small hm]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem measurable_freq {χ : W → W → ℂ} (h : IsBichar χ) (v : W) (β : W → ℝ)
    (hβ : ∀ y, ∀ s : ℝ, χ (s • v) y = exp (↑(β y * s) * I)) : Measurable β := by
  let g : ℕ → W → ℝ := fun m y => ((m : ℝ) + 1) * arg (χ ((1 / ((m : ℝ) + 1)) • v) y)
  have hg : ∀ m, Measurable (g m) := fun m =>
    measurable_const.mul (measurable_arg.comp (h.contR _).measurable)
  refine measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.2 fun y => ?_)
  have ht : Tendsto (fun m : ℕ => β y * (1 / ((m : ℝ) + 1))) atTop (𝓝 (β y * 0)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (β y)
  rw [mul_zero] at ht
  have hev := ht (Ioo_mem_nhds (neg_lt_zero.2 Real.pi_pos) Real.pi_pos)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with m hm
  simp only [g]
  rw [hβ y, arg_exp_small hm]
  field_simp

/- English proof (translation)
Use `freq_unique fun s => ?_` and prove the remaining obligations. Rewrite using `[← hβ, h.addR, hβ, hβ, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem freq_add {χ : W → W → ℂ} (h : IsBichar χ) (v : W) (β : W → ℝ)
    (hβ : ∀ y, ∀ s : ℝ, χ (s • v) y = exp (↑(β y * s) * I)) (y y' : W) :
    β (y + y') = β y + β y' := by
  refine freq_unique fun s => ?_
  rw [← hβ, h.addR, hβ, hβ, ← Complex.exp_add]
  congr 1; push_cast; ring

/- English proof (translation)
Use `choose β hβ using fun v y => h.freq v y`. Set `b` to `stdOrthonormalBasis ℝ W`. Establish `hm : ∀ j, Measurable (fun y => β (b j) y)` using `fun j => measurable_freq h (b j) _ (fun y => hβ (b j) y)`. Establish `ha : ∀ j y y', β (b j) (y + y') = β (b j) y + β (b j) y'` using `fun j => freq_add h (b j) (fun y => β (b j) y) (fun y => hβ (b j) y)`. Set `Lf : W → W` to `fun y => ∑ j, (β (b j) y / (2 * Real.pi)) • b j`.

Set `Lm : W →+ W` to `AddMonoidHom.mk' Lf fun y y' => by`. Simplify using `only [Lf, ha, add_div, add_smul, Finset.sum_add_distrib]`. Establish `hLm : Measurable Lm` using `by show Measurable fun y => ∑ j, (β (b j) y / (2 * Real.pi)) • b j`. Conclude with `Finset.measurable_sum Finset.univ fun j _ => ((hm j).div_const _).smul_const (b j)`. Establish `hLc : Continuous Lm` using `Measure.AddMonoidHom.continuous_of_measurable Lm hLm`.

Use `⟨Lm.toRealLinearMap hLc, fun x y => ?_⟩` and prove the remaining obligations. Establish `hprod : ∀ s : Finset (Fin (Module.finrank ℝ W)), χ (∑ j ∈ s, ⟪b j, x⟫ • b j) y = ∏ j ∈ s, χ (⟪b j, x⟫ • b j) y`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [h.zero_left]`.

Consider the case `insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, h.addL, ih]`. Establish `e1 : χ x y = χ (∑ j, ⟪b j, x⟫ • b j) y` using `by rw [b.sum_repr' x]`. Rewrite using `[e1, hprod]`. Establish `e2 : ∀ j, χ (⟪b j, x⟫ • b j) y = exp (↑(β (b j) y * ⟪b j, x⟫) * I)` using `fun j => hβ _ _ _`. Simplify using `only [e2]`.

Rewrite using `[← Complex.exp_sum, Real.fourierChar_apply]`. Use `congr 1`. Establish `hLy : ⟪x, (Lm.toRealLinearMap hLc) y⟫ = ∑ j, β (b j) y / (2 * Real.pi) * ⟪b j, x⟫` using `by show ⟪x, Lf y⟫ = _`. Simplify using `only [Lf, inner_sum, inner_smul_right]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [real_inner_comm]`.

Rewrite using `[hLy]`. Use `push_cast`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `: (Real.pi : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 Real.pi_ne_zero`.

Clear the denominators using the available nonvanishing facts.
-/
theorem bichar_eq {χ : W → W → ℂ} (h : IsBichar χ) :
    ∃ L : W →L[ℝ] W, ∀ x y, χ x y = (Real.fourierChar ⟪x, L y⟫ : ℂ) := by
  classical
  choose β hβ using fun v y => h.freq v y
  let b := stdOrthonormalBasis ℝ W
  have hm : ∀ j, Measurable (fun y => β (b j) y) := fun j =>
    measurable_freq h (b j) _ (fun y => hβ (b j) y)
  have ha : ∀ j y y', β (b j) (y + y') = β (b j) y + β (b j) y' := fun j =>
    freq_add h (b j) (fun y => β (b j) y) (fun y => hβ (b j) y)
  let Lf : W → W := fun y => ∑ j, (β (b j) y / (2 * Real.pi)) • b j
  let Lm : W →+ W := AddMonoidHom.mk' Lf fun y y' => by
    simp only [Lf, ha, add_div, add_smul, Finset.sum_add_distrib]
  have hLm : Measurable Lm := by
    show Measurable fun y => ∑ j, (β (b j) y / (2 * Real.pi)) • b j
    exact Finset.measurable_sum Finset.univ fun j _ => ((hm j).div_const _).smul_const (b j)
  have hLc : Continuous Lm := Measure.AddMonoidHom.continuous_of_measurable Lm hLm
  refine ⟨Lm.toRealLinearMap hLc, fun x y => ?_⟩
  have hprod : ∀ s : Finset (Fin (Module.finrank ℝ W)),
      χ (∑ j ∈ s, ⟪b j, x⟫ • b j) y = ∏ j ∈ s, χ (⟪b j, x⟫ • b j) y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [h.zero_left]
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, h.addL, ih]
  have e1 : χ x y = χ (∑ j, ⟪b j, x⟫ • b j) y := by rw [b.sum_repr' x]
  rw [e1, hprod]
  have e2 : ∀ j, χ (⟪b j, x⟫ • b j) y = exp (↑(β (b j) y * ⟪b j, x⟫) * I) := fun j => hβ _ _ _
  simp only [e2]
  rw [← Complex.exp_sum, Real.fourierChar_apply]
  congr 1
  have hLy : ⟪x, (Lm.toRealLinearMap hLc) y⟫ = ∑ j, β (b j) y / (2 * Real.pi) * ⟪b j, x⟫ := by
    show ⟪x, Lf y⟫ = _
    simp only [Lf, inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm]
  rw [hLy]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

end Bichar

section Tests

open scoped RealInnerProductSpace FourierTransform SchwartzMap ContDiff

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/- English proof (translation)
Establish `hpos : 0 < ‖t‖` using `norm_pos_iff.2 ht0`. Set `f : ContDiffBump (0 : W)` to `⟨‖t‖ / 4, ‖t‖ / 2, by positivity, by linarith⟩`. Set `φ : W → ℂ` to `fun x => ((f x : ℝ) : ℂ)`. Establish `hφc : Continuous φ` using `Complex.continuous_ofReal.comp f.continuous`. Establish `hφs : HasCompactSupport φ` using `f.hasCompactSupport.comp_left Complex.ofReal_zero`.

Set `Φ : W → ℂ` to `fun x => φ (x + t) - φ x`. Establish `hΦc : Continuous Φ` using `(hφc.comp (continuous_id.add continuous_const)).sub hφc`. Establish `hΦs : HasCompactSupport Φ`. Establish `h1 : HasCompactSupport fun x => φ (x + t)` using `hφs.comp_homeomorph (Homeomorph.addRight t)`. Conclude with `h1.sub hφs`.

Establish `hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = 0`. Introduce `y`. Set `g : W → ℂ` to `fun x => φ x * χ x y`. Establish `hg : Integrable g μ` using `(hφc.mul (hc y)).integrable_of_hasCompactSupport hφs.mul_right`. Establish `e : (fun x => Φ x * χ x y) = fun x => g (x + t) - g x`.

Use function extensionality and compare the values at `x`. Simplify using `only [Φ, g, hadd, ht, mul_one, sub_mul]`. Rewrite using `[e, integral_sub (hg.comp_add_right t) hg, integral_add_right_eq_self, sub_self]`. Use `⟨Φ, hΦc, hΦs, ?_, 0, ?_⟩` and prove the remaining obligations. Establish `e : (fun y => ∫ x, Φ x * χ x y ∂μ) = fun _ => 0` using `funext hT`.

Rewrite using `[e]`. Conclude with `integrable_zero _ _ _`. Simplify using `only [Φ, φ, neg_zero, zero_add]`. Rewrite using `[f.zero_of_le_dist (by rw [dist_zero_right]; show ‖t‖ / 2 ≤ ‖t‖; linarith), f.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))]`. Evaluate the numerical expressions.
-/
theorem testEx_kernel (μ : Measure W) [μ.IsAddHaarMeasure] (χ : W → W → ℂ)
    (hadd : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hc : ∀ y, Continuous fun x => χ x y)
    (t : W) (ht0 : t ≠ 0) (ht : ∀ y, χ t y = 1) : SdUniqW.TestEx μ χ := by
  have hpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  let f : ContDiffBump (0 : W) := ⟨‖t‖ / 4, ‖t‖ / 2, by positivity, by linarith⟩
  let φ : W → ℂ := fun x => ((f x : ℝ) : ℂ)
  have hφc : Continuous φ := Complex.continuous_ofReal.comp f.continuous
  have hφs : HasCompactSupport φ := f.hasCompactSupport.comp_left Complex.ofReal_zero
  let Φ : W → ℂ := fun x => φ (x + t) - φ x
  have hΦc : Continuous Φ := (hφc.comp (continuous_id.add continuous_const)).sub hφc
  have hΦs : HasCompactSupport Φ := by
    have h1 : HasCompactSupport fun x => φ (x + t) := hφs.comp_homeomorph (Homeomorph.addRight t)
    exact h1.sub hφs
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = 0 := by
    intro y
    let g : W → ℂ := fun x => φ x * χ x y
    have hg : Integrable g μ := (hφc.mul (hc y)).integrable_of_hasCompactSupport hφs.mul_right
    have e : (fun x => Φ x * χ x y) = fun x => g (x + t) - g x := by
      funext x; simp only [Φ, g, hadd, ht, mul_one, sub_mul]
    rw [e, integral_sub (hg.comp_add_right t) hg, integral_add_right_eq_self, sub_self]
  refine ⟨Φ, hΦc, hΦs, ?_, 0, ?_⟩
  · have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = fun _ => 0 := funext hT
    rw [e]; exact integrable_zero _ _ _
  · simp only [Φ, φ, neg_zero, zero_add]
    rw [f.zero_of_le_dist (by rw [dist_zero_right]; show ‖t‖ / 2 ≤ ‖t‖; linarith),
      f.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))]
    norm_num

/- English proof (translation)
Set `f : ContDiffBump (0 : W)` to `⟨1, 2, one_pos, one_lt_two⟩`. Set `φ : W → ℂ` to `fun x => ((f x : ℝ) : ℂ)`. Establish `hφd : ContDiff ℝ ∞ φ` using `Complex.ofRealCLM.contDiff.comp f.contDiff`. Establish `hφs : HasCompactSupport φ` using `f.hasCompactSupport.comp_left Complex.ofReal_zero`. Set `S : 𝓢(W, ℂ)` to `hφs.toSchwartzMap hφd`.

Set `B : W ≃L[ℝ] W` to `A.trans (ContinuousLinearEquiv.neg ℝ)`. Use `set c : NNReal := μ.addHaarScalarFactor volume`. Establish `hμ : μ = c • volume` using `Measure.isAddLeftInvariant_eq_smul μ volume`. Establish `hT : ∀ y, ∫ x, φ x * (Real.fourierChar ⟪x, A y⟫ : ℂ) ∂μ = ((c : ℝ) : ℂ) * (𝓕 S : 𝓢(W, ℂ)) (B y)`. Introduce `y`.

Rewrite using `[hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`. Use `congr 1`. Rewrite using `[SchwartzMap.fourier_coe, Real.fourier_eq]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `[B, S, φ, inner_neg_right, Circle.smul_def, mul_comm]`.

Establish `hB : (Measure.map B μ).IsAddHaarMeasure` using `B.isAddHaarMeasure_map μ`. Establish `hI : Integrable (fun y => (𝓕 S : 𝓢(W, ℂ)) (B y)) μ`. Establish `h1 : Integrable (𝓕 S : 𝓢(W, ℂ)) (Measure.map B μ)` using `(𝓕 S).integrable`. Conclude with `(integrable_map_measure h1.aestronglyMeasurable B.continuous.measurable.aemeasurable).1 h1`. Use `⟨φ, hφd.continuous, hφs, ?_, 0, ?_⟩` and prove the remaining obligations.

Establish `e : (fun y => ∫ x, φ x * (Real.fourierChar ⟪x, A y⟫ : ℂ) ∂μ) = fun y => ((c : ℝ) : ℂ) * (𝓕 S : 𝓢(W, ℂ)) (B y)` using `funext hT`. Rewrite using `[e]`. Conclude with `hI.const_mul _`. Simplify using `only [φ, neg_zero]`. Rewrite using `[f.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]`.

Evaluate the numerical expressions.
-/
theorem testEx_fourier (μ : Measure W) [μ.IsAddHaarMeasure] (A : W ≃L[ℝ] W) :
    SdUniqW.TestEx μ (fun x y => (Real.fourierChar ⟪x, A y⟫ : ℂ)) := by
  let f : ContDiffBump (0 : W) := ⟨1, 2, one_pos, one_lt_two⟩
  let φ : W → ℂ := fun x => ((f x : ℝ) : ℂ)
  have hφd : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp f.contDiff
  have hφs : HasCompactSupport φ := f.hasCompactSupport.comp_left Complex.ofReal_zero
  let S : 𝓢(W, ℂ) := hφs.toSchwartzMap hφd
  let B : W ≃L[ℝ] W := A.trans (ContinuousLinearEquiv.neg ℝ)
  set c : NNReal := μ.addHaarScalarFactor volume
  have hμ : μ = c • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  have hT : ∀ y, ∫ x, φ x * (Real.fourierChar ⟪x, A y⟫ : ℂ) ∂μ =
      ((c : ℝ) : ℂ) * (𝓕 S : 𝓢(W, ℂ)) (B y) := by
    intro y
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    congr 1
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [B, S, φ, inner_neg_right, Circle.smul_def, mul_comm]
  have hB : (Measure.map B μ).IsAddHaarMeasure := B.isAddHaarMeasure_map μ
  have hI : Integrable (fun y => (𝓕 S : 𝓢(W, ℂ)) (B y)) μ := by
    have h1 : Integrable (𝓕 S : 𝓢(W, ℂ)) (Measure.map B μ) := (𝓕 S).integrable
    exact (integrable_map_measure h1.aestronglyMeasurable B.continuous.measurable.aemeasurable).1 h1
  refine ⟨φ, hφd.continuous, hφs, ?_, 0, ?_⟩
  · have e : (fun y => ∫ x, φ x * (Real.fourierChar ⟪x, A y⟫ : ℂ) ∂μ) =
        fun y => ((c : ℝ) : ℂ) * (𝓕 S : 𝓢(W, ℂ)) (B y) := funext hT
    rw [e]; exact hI.const_mul _
  · simp only [φ, neg_zero]
    rw [f.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
    norm_num

/- English proof (translation)
Take `⟨L, hL⟩` from `bichar_eq h`. Distinguish the cases in `hs : Function.Surjective L`. Establish `hi : Function.Injective L` using `(LinearMap.injective_iff_surjective (f := (L : W →ₗ[ℝ] W))).2 hs`. Set `A : W ≃L[ℝ] W` to `(LinearEquiv.ofBijective (L : W →ₗ[ℝ] W) ⟨hi, hs⟩).toContinuousLinearEquiv`. Establish `e : χ = fun x y => (Real.fourierChar ⟪x, A y⟫ : ℂ)` using `funext₂ fun x y => by rw [hL x y]; rfl`.

Rewrite using `[e]`. Conclude with `testEx_fourier μ A`. Establish `hK : (LinearMap.range (L : W →ₗ[ℝ] W))ᗮ ≠ ⊥`. Rewrite using `[Ne, Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]`. Conclude with `hs`.

Take `⟨t, htK, ht0⟩` from `(Submodule.ne_bot_iff _).1 hK`. Use `testEx_kernel μ χ h.addL h.contL t ht0 fun y => ?_` and prove the remaining obligations. Establish `h0 : ⟪t, L y⟫ = 0` using `(Submodule.mem_orthogonal' _ t).1 htK _ (LinearMap.mem_range_self (L : W →ₗ[ℝ] W) y)`. Rewrite using `[hL, h0, AddChar.map_zero_eq_one, Circle.coe_one]`.
-/
theorem testEx_bichar (μ : Measure W) [μ.IsAddHaarMeasure] {χ : W → W → ℂ} (h : IsBichar χ) :
    SdUniqW.TestEx μ χ := by
  obtain ⟨L, hL⟩ := bichar_eq h
  by_cases hs : Function.Surjective L
  · have hi : Function.Injective L :=
      (LinearMap.injective_iff_surjective (f := (L : W →ₗ[ℝ] W))).2 hs
    let A : W ≃L[ℝ] W :=
      (LinearEquiv.ofBijective (L : W →ₗ[ℝ] W) ⟨hi, hs⟩).toContinuousLinearEquiv
    have e : χ = fun x y => (Real.fourierChar ⟪x, A y⟫ : ℂ) :=
      funext₂ fun x y => by rw [hL x y]; rfl
    rw [e]; exact testEx_fourier μ A
  · have hK : (LinearMap.range (L : W →ₗ[ℝ] W))ᗮ ≠ ⊥ := by
      rw [Ne, Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]; exact hs
    obtain ⟨t, htK, ht0⟩ := (Submodule.ne_bot_iff _).1 hK
    refine testEx_kernel μ χ h.addL h.contL t ht0 fun y => ?_
    have h0 : ⟪t, L y⟫ = 0 :=
      (Submodule.mem_orthogonal' _ t).1 htK _ (LinearMap.mem_range_self (L : W →ₗ[ℝ] W) y)
    rw [hL, h0, AddChar.map_zero_eq_one, Circle.coe_one]

/- English proof (translation)
Set `ea : V ≃+ W` to `AddEquiv.mk' e.toEquiv he`. Establish `hs : ∀ u v : W, e.symm (u + v) = e.symm u + e.symm v` using `fun u v => ea.symm.map_add u v`. Set `ce : V ≃ₜ+ W` to `{ ea with continuous_toFun := e.continuous, continuous_invFun := e.symm.continuous }`. Set `em : V ≃ᵐ W` to `e.toMeasurableEquiv`. Set `μ' : Measure W` to `Measure.map em μ`.

Establish `: μ'.IsAddHaarMeasure` using `ContinuousAddEquiv.isAddHaarMeasure_map μ ce`. Set `χ' : W → W → ℂ` to `fun x y => χ (e.symm x) (e.symm y)`. Establish `hb : IsBichar χ'` using `{ addL := fun x x' y => by simp only [χ', hs, hL] addR := fun x y y' => by simp only [χ', hs, hR] norm1 := fun x y => hn _ _ contL := fun y => (hcL _).comp e.symm.continuous contR := fun x => (hcR _).comp e.symm.continuous }`. Take `⟨φ, hφc, hφs, hI, z, hz⟩` from `testEx_bichar μ' hb`. Establish `hT : ∀ y, ∫ x, φ (e x) * χ x y ∂μ = ∫ x, φ x * χ' x (e y) ∂μ'`.

Introduce `y`. Rewrite using `[integral_map_equiv em]`. Simplify using `[χ', em]`. Use `⟨fun x => φ (e x), hφc.comp e.continuous, hφs.comp_homeomorph e, ?_, e.symm z, ?_⟩` and prove the remaining obligations. Use `show Integrable (fun y => ∫ x, φ (e x) * χ x y ∂μ) μ`.

Establish `e1 : (fun y => ∫ x, φ (e x) * χ x y ∂μ) = (fun y => ∫ x, φ x * χ' x y ∂μ') ∘ em`. Use function extensionality and compare the values at `hT`. Rewrite using `[e1]`. Conclude with `(integrable_map_equiv em _).1 hI`. Use `show φ (e (-e.symm z)) ≠ 0`.

Establish `h1 : e (-e.symm z) = -z`. Use `ea.map_neg (e.symm z)` as an intermediate fact. Express the relevant statement in the definitionally equal form `e (-e.symm z) = -e (e.symm z) at this`. Rewrite using `[this, e.apply_symm_apply]`. Rewrite using `[h1]`.

Conclude with `hz`.
-/
theorem testEx_of_homeo {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
    (e : V ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y)
    (hL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hR : ∀ x y y', χ x (y + y') = χ x y * χ x y')
    (hn : ∀ x y, ‖χ x y‖ = 1) (hcL : ∀ y, Continuous fun x => χ x y)
    (hcR : ∀ x, Continuous (χ x)) : SdUniqW.TestEx μ χ := by
  let ea : V ≃+ W := AddEquiv.mk' e.toEquiv he
  have hs : ∀ u v : W, e.symm (u + v) = e.symm u + e.symm v := fun u v => ea.symm.map_add u v
  let ce : V ≃ₜ+ W :=
    { ea with continuous_toFun := e.continuous, continuous_invFun := e.symm.continuous }
  let em : V ≃ᵐ W := e.toMeasurableEquiv
  let μ' : Measure W := Measure.map em μ
  have : μ'.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ ce
  let χ' : W → W → ℂ := fun x y => χ (e.symm x) (e.symm y)
  have hb : IsBichar χ' :=
    { addL := fun x x' y => by simp only [χ', hs, hL]
      addR := fun x y y' => by simp only [χ', hs, hR]
      norm1 := fun x y => hn _ _
      contL := fun y => (hcL _).comp e.symm.continuous
      contR := fun x => (hcR _).comp e.symm.continuous }
  obtain ⟨φ, hφc, hφs, hI, z, hz⟩ := testEx_bichar μ' hb
  have hT : ∀ y, ∫ x, φ (e x) * χ x y ∂μ = ∫ x, φ x * χ' x (e y) ∂μ' := by
    intro y
    rw [integral_map_equiv em]
    simp [χ', em]
  refine ⟨fun x => φ (e x), hφc.comp e.continuous, hφs.comp_homeomorph e, ?_, e.symm z, ?_⟩
  · show Integrable (fun y => ∫ x, φ (e x) * χ x y ∂μ) μ
    have e1 : (fun y => ∫ x, φ (e x) * χ x y ∂μ) = (fun y => ∫ x, φ x * χ' x y ∂μ') ∘ em :=
      funext hT
    rw [e1]
    exact (integrable_map_equiv em _).1 hI
  · show φ (e (-e.symm z)) ≠ 0
    have h1 : e (-e.symm z) = -z := by
      have := ea.map_neg (e.symm z)
      change e (-e.symm z) = -e (e.symm z) at this
      rw [this, e.apply_symm_apply]
    rw [h1]; exact hz

end Tests

section Adelic

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation PI.VolFromSW SdUniqW

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Simplify using `only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem BR_add_right' (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y Y' : Fin n → Fin M → R ⊗[F] E) : BR R σ J X (Y + Y') = BR R σ J X Y + BR R σ J X Y' := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]`.
-/
theorem pairHerm_add_right' (σ : E →ₐ[F] E) (n : ℕ) (S T U : HermR R σ n) :
    pairHerm R σ n S (T + U) = pairHerm R σ n S T + pairHerm R σ n S U := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, mul_add, Finset.sum_add_distrib,
    map_add]

end Alg

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

/- English proof (translation)
Establish `h : ∀ a : Fin n, Continuous fun X : Fin n → Fin M → R ⊗[F] E => Algebra.trace R (R ⊗[F] E) (hR R σ J (X a) (Y a))`. Introduce `a`. Establish `h0 : Continuous fun X : Fin n → Fin M → R ⊗[F] E => (X a, Y a)` using `(continuous_apply a).prodMk (continuous_const (y := Y a))`. Establish `hc` using `continuous_hR R σ J`. Establish `h1` using `Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) => hR R σ J q.1 q.2) hc h0`.

Establish `h2 : Continuous fun z : R ⊗[F] E => Algebra.trace R (R ⊗[F] E) z` using `continuous_trace_tens R`. Conclude with `h2.comp h1`. Conclude with `continuous_finsetSum Finset.univ fun a _ => h a`.
-/
theorem continuous_BR_left (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → R ⊗[F] E) : Continuous fun X => BR R σ J X Y := by
  have h : ∀ a : Fin n, Continuous fun X : Fin n → Fin M → R ⊗[F] E =>
      Algebra.trace R (R ⊗[F] E) (hR R σ J (X a) (Y a)) := by
    intro a
    have h0 : Continuous fun X : Fin n → Fin M → R ⊗[F] E => (X a, Y a) :=
      (continuous_apply a).prodMk (continuous_const (y := Y a))
    have hc := continuous_hR R σ J
    have h1 := Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) =>
      hR R σ J q.1 q.2) hc h0
    have h2 : Continuous fun z : R ⊗[F] E => Algebra.trace R (R ⊗[F] E) z := continuous_trace_tens R
    exact h2.comp h1
  exact continuous_finsetSum Finset.univ fun a _ => h a

/- English proof (translation)
Use `show Continuous fun S : HermR R σ n => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (∑ a, ∑ b, (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * (T : Matrix (Fin n) (Fin n) _) b a)`. Use `continuous_const.mul ((continuous_trace_tens R).comp ?_)` and prove the remaining obligations. Use `continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_` and prove the remaining obligations. Conclude with `(Continuous.matrix_elem continuous_subtype_val a b).mul continuous_const`.
-/
theorem continuous_pairHerm_left (σ : E →ₐ[F] E) (n : ℕ) (T : HermR R σ n) :
    Continuous fun S : HermR R σ n => pairHerm R σ n S T := by
  show Continuous fun S : HermR R σ n => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
    (∑ a, ∑ b, (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * (T : Matrix (Fin n) (Fin n) _) b a)
  refine continuous_const.mul ((continuous_trace_tens R).comp ?_)
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (Continuous.matrix_elem continuous_subtype_val a b).mul continuous_const

end Top

/- English proof (translation)
Establish `: Continuous fun x : Ainf F => ((x, (0 : Af F)) : Ainf F × Af F)` using `continuous_id.prodMk continuous_const`. Conclude with `hψ.comp this`.
-/
theorem continuous_psiInf' {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) : Continuous (psiInf F ψ) := by
  have : Continuous fun x : Ainf F => ((x, (0 : Af F)) : Ainf F × Af F) :=
    continuous_id.prodMk continuous_const
  exact hψ.comp this

/- English proof (translation)
Set `L` to `(EuclideanSpace.equiv (Fin n) ℝ).symm`. Use `testEx_of_homeo μ χ (e.trans L.toHomeomorph) (fun x y => ?_) hL hR hn hcL hcR` and prove the remaining obligations. Use `show L (e (x + y)) = L (e x) + L (e y)`. Rewrite using `[he, map_add]`.
-/
theorem testEx_coord {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
    {n : ℕ} (e : V ≃ₜ (Fin n → ℝ)) (he : ∀ x y, e (x + y) = e x + e y)
    (hL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hR : ∀ x y y', χ x (y + y') = χ x y * χ x y')
    (hn : ∀ x y, ‖χ x y‖ = 1) (hcL : ∀ y, Continuous fun x => χ x y)
    (hcR : ∀ x, Continuous (χ x)) : TestEx μ χ := by
  let L := (EuclideanSpace.equiv (Fin n) ℝ).symm
  refine testEx_of_homeo μ χ (e.trans L.toHomeomorph) (fun x y => ?_) hL hR hn hcL hcR
  show L (e (x + y)) = L (e x) + L (e y)
  rw [he, map_add]

end Adelic

end SdTestInfW

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation PI.VolFromSW SdUniqW SdTestInfW

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Take `⟨n, m, eV, eH, hV, hH⟩` from `tensR_holds F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet`. Establish `: SecondCountableTopology (HermR (Ainf F) σ a)`. Establish `: SecondCountableTopology (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E))` using `inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ainf F ⊗[F] E))`.

Use the proof step `Topology.IsInducing.subtypeVal.secondCountableTopology`. Establish `hpc` using `continuous_psiInf' ψ hψ.1`. Establish `hpn : ∀ r, ‖psiInf F ψ r‖ = 1` using `fun r => hψ.2.1 _`. Use `⟨fun μ hμ => ?_, fun ν hν => ?_⟩` and prove the remaining obligations. Use `hμ.1` as an intermediate fact.

Conclude with `testEx_coord μ _ eV hV (fun X X' Y => by rw [BR_add, psiInf_add]) (fun X Y Y' => by rw [BR_add_right', psiInf_add]) (fun X Y => hpn _) (fun Y => hpc.comp (continuous_BR_left (Ainf F) σ J Y)) (fun X => hpc.comp (continuous_BR_right (Ainf F) σ J X))`. Use `hν.1` as an intermediate fact. Conclude with `testEx_coord ν _ eH hH (fun S S' T => by rw [pairHerm_add, psiInf_add]) (fun S T T' => by rw [pairHerm_add_right', psiInf_add]) (fun S T => hpn _) (fun T => hpc.comp (continuous_pairHerm_left (Ainf F) σ a T)) (fun S => hpc.comp (continuous_pairHerm_right (Ainf F) σ a S))`.
-/
theorem sdTestInf_holds : SdTestInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨n, m, eV, eH, hV, hH⟩ := tensR_holds F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet
  have : SecondCountableTopology (HermR (Ainf F) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ainf F ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  have hpc := continuous_psiInf' ψ hψ.1
  have hpn : ∀ r, ‖psiInf F ψ r‖ = 1 := fun r => hψ.2.1 _
  refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
  · have := hμ.1
    exact testEx_coord μ _ eV hV (fun X X' Y => by rw [BR_add, psiInf_add])
      (fun X Y Y' => by rw [BR_add_right', psiInf_add]) (fun X Y => hpn _)
      (fun Y => hpc.comp (continuous_BR_left (Ainf F) σ J Y))
      (fun X => hpc.comp (continuous_BR_right (Ainf F) σ J X))
  · have := hν.1
    exact testEx_coord ν _ eH hH (fun S S' T => by rw [pairHerm_add, psiInf_add])
      (fun S T T' => by rw [pairHerm_add_right', psiInf_add]) (fun S T => hpn _)
      (fun T => hpc.comp (continuous_pairHerm_left (Ainf F) σ a T))
      (fun S => hpc.comp (continuous_pairHerm_right (Ainf F) σ a S))

end PI.VolStabW
