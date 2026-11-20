import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.CharDensity

open scoped FourierTransform
open Filter

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

noncomputable def phi (μ : Measure V) (x : V) : ℂ :=
  ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ z x : ℝ) : ℂ)) ∂μ

/- English proof (translation)
Unfold `phi`. Rewrite using `[charFun_apply]`. Use `integral_congr_ae (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [inner_smul_right]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma phi_eq_charFun (μ : Measure V) (x : V) :
    phi μ x = charFun μ ((2 * Real.pi) • x) := by
  unfold phi
  rw [charFun_apply]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [inner_smul_right]
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish `: phi μ = fun x => charFun μ ((2 * Real.pi) • x)` using `funext (phi_eq_charFun μ)`. Rewrite using `[this]`. Conclude with `continuous_charFun.comp (continuous_const_smul _)`.
-/
lemma continuous_phi (μ : Measure V) [IsFiniteMeasure μ] : Continuous (phi μ) := by
  have : phi μ = fun x => charFun μ ((2 * Real.pi) • x) := funext (phi_eq_charFun μ)
  rw [this]
  exact continuous_charFun.comp (continuous_const_smul _)

noncomputable def ker (b : ℝ) (w : V) : ℝ :=
  (Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 / b) * ‖w‖ ^ 2)

/- English proof (translation)
Unfold `ker`. Use `Real.pi_pos` as an intermediate fact. Check the signs of the components of the expression.
-/
lemma ker_nonneg {b : ℝ} (hb : 0 < b) (w : V) : 0 ≤ ker b w := by
  unfold ker
  have := Real.pi_pos
  positivity

/- English proof (translation)
Unfold `ker`. Use `fun_prop`.
-/
lemma continuous_ker (b : ℝ) : Continuous (ker b : V → ℝ) := by
  unfold ker
  fun_prop

/- English proof (translation)
Unfold `ker`. Establish `hp` using `Real.pi_pos`. Use `mul_le_of_le_one_right (by positivity) ?_` and prove the remaining obligations. Rewrite using `[Real.exp_le_one_iff]`. Establish `: 0 ≤ Real.pi ^ 2 / b * ‖w‖ ^ 2` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma ker_le {b : ℝ} (hb : 0 < b) (w : V) :
    ker b w ≤ (Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  unfold ker
  have hp := Real.pi_pos
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [Real.exp_le_one_iff]
  have : 0 ≤ Real.pi ^ 2 / b * ‖w‖ ^ 2 := by positivity
  linarith

/- English proof (translation)
Establish `h` using `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (b : ℂ)) (by simpa using hb) 0 0`. Establish `h2` using `h.norm`. Use `h2.congr (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[Complex.norm_exp, ← Complex.ofReal_pow]`.
-/
lemma integrable_gauss {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : V => Real.exp (-b * ‖x‖ ^ 2)) volume := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V)
    (b := (b : ℂ)) (by simpa using hb) 0 0
  have h2 := h.norm
  refine h2.congr (Eventually.of_forall fun x => ?_)
  simp [Complex.norm_exp, ← Complex.ofReal_pow]

/- English proof (translation)
Establish `hp` using `Real.pi_pos`. Conclude with `(integrable_gauss (V := V) (b := Real.pi ^ 2 / b) (by positivity)).const_mul _`.
-/
lemma integrable_ker {b : ℝ} (hb : 0 < b) : Integrable (ker b : V → ℝ) volume := by
  have hp := Real.pi_pos
  exact (integrable_gauss (V := V) (b := Real.pi ^ 2 / b) (by positivity)).const_mul _

/- English proof (translation)
Establish `hp` using `Real.pi_pos`. Unfold `ker`. Rewrite using `[integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity), ← Real.mul_rpow (by positivity) (by positivity)]`. Establish `: Real.pi / b * (Real.pi / (Real.pi ^ 2 / b)) = 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this, Real.one_rpow]`.
-/
lemma integral_ker {b : ℝ} (hb : 0 < b) : ∫ w : V, ker b w = 1 := by
  have hp := Real.pi_pos
  unfold ker
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity),
    ← Real.mul_rpow (by positivity) (by positivity)]
  have : Real.pi / b * (Real.pi / (Real.pi ^ 2 / b)) = 1 := by
    field_simp
  rw [this, Real.one_rpow]

/- English proof (translation)
Establish `hp` using `Real.pi_pos`. Rewrite using `[GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using hb)]`. Unfold `ker`. Use `push_cast`. Establish `hb' : (b : ℂ) ≠ 0` using `by exact_mod_cast hb.ne'`.

Rewrite using `[Complex.ofReal_cpow (by positivity)]`. Use `push_cast`. Use `congr 2`. Establish `hI : Complex.I ^ 2 = -1` using `Complex.I_sq`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hI]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma gauss_inner {b : ℝ} (hb : 0 < b) (u : V) :
    ∫ x : V, Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2 +
      (2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ u x : ℝ) : ℂ)) = (ker b u : ℂ) := by
  have hp := Real.pi_pos
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using hb)]
  unfold ker
  push_cast
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 2
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  field_simp
  rw [hI]
  ring

/- English proof (translation)
Use `set F : V → V → ℂ := fun x z => Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2 + (2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ (z - y) x : ℝ) : ℂ)) with hF`. Establish `h1 : ∀ x, phi μ x * (Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))) = ∫ z, F x z ∂μ`. Introduce `x`. Unfold `phi`. Rewrite using `[← integral_mul_const]`.

Use `integral_congr_ae (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [hF, ← Complex.exp_add, inner_sub_left]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hint : Integrable (Function.uncurry F) ((volume : Measure V).prod μ)`. Establish `hg` using `(integrable_gauss (V := V) hb).comp_fst μ`. Use `hg.mono' ?_ (Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Apply `Continuous.aestronglyMeasurable` to reduce the goal to its premises. Simplify using `only [hF, Function.uncurry_def]`.

Use `fun_prop`. Simplify using `only [Function.uncurry_def, hF, Complex.norm_exp]`. Apply `le_of_eq` to reduce the goal to its premises. Use `congr 1`. Simplify using `[← Complex.ofReal_pow, Complex.mul_re, Complex.add_re]`.

Repeatedly rewrite using `[h1]`. Rewrite using `[integral_integral_swap hint, ← integral_complex_ofReal]`. Use `integral_congr_ae (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Conclude with `gauss_inner hb _`.
-/
lemma smoothed_eq (μ : Measure V) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) (y : V) :
    ∫ x, phi μ x * (Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))) =
      ((∫ z, ker b (z - y) ∂μ : ℝ) : ℂ) := by
  set F : V → V → ℂ := fun x z => Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2 +
      (2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ (z - y) x : ℝ) : ℂ)) with hF
  have h1 : ∀ x, phi μ x * (Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))) =
      ∫ z, F x z ∂μ := by
    intro x
    unfold phi
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hF, ← Complex.exp_add, inner_sub_left]
    congr 1
    push_cast
    ring
  have hint : Integrable (Function.uncurry F) ((volume : Measure V).prod μ) := by
    have hg := (integrable_gauss (V := V) hb).comp_fst μ
    refine hg.mono' ?_ (Eventually.of_forall fun p => ?_)
    · apply Continuous.aestronglyMeasurable
      simp only [hF, Function.uncurry_def]
      fun_prop
    · simp only [Function.uncurry_def, hF, Complex.norm_exp]
      apply le_of_eq
      congr 1
      simp [← Complex.ofReal_pow, Complex.mul_re, Complex.add_re]
  simp_rw [h1]
  rw [integral_integral_swap hint, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  exact gauss_inner hb _

noncomputable def dens (μ : Measure V) (y : V) : ℂ :=
  ∫ x, phi μ x * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))

/- English proof (translation)
Rewrite using `[Real.fourier_eq']`. Unfold `dens`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Rewrite using `[mul_comm, real_inner_comm]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma dens_eq_fourier (μ : Measure V) (y : V) : dens μ y = 𝓕 (phi μ) y := by
  rw [Real.fourier_eq']
  unfold dens
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm, real_inner_comm]
  congr 2
  push_cast
  ring

noncomputable def bn (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/- English proof (translation)
Unfold `bn`. Check the signs of the components of the expression.
-/
lemma bn_pos (n : ℕ) : 0 < bn n := by
  unfold bn
  positivity

/- English proof (translation)
Repeatedly rewrite using `[← smoothed_eq μ (bn_pos _) y]`. Unfold `dens`. Establish `hcp` using `continuous_phi μ`. Use `tendsto_integral_of_dominated_convergence (fun x => ‖phi μ x‖) (fun n => ?_) hφ.norm (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Apply `Continuous.aestronglyMeasurable fun_prop` to reduce the goal to its premises.

Rewrite using `[norm_mul, norm_mul]`. Use `mul_le_of_le_one_right (norm_nonneg _) ?_` and prove the remaining obligations. Establish `h2 : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))‖ = 1`. Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules.

Establish `h1 : ‖Complex.exp (-(bn n : ℂ) * (‖x‖ : ℂ) ^ 2)‖ ≤ 1`. Rewrite using `[Complex.norm_exp, Real.exp_le_one_iff]`. Use `(bn_pos n).le` as an intermediate fact. Simplify using `only [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]`. Use polynomial arithmetic with `[sq_nonneg ‖x‖]`.

Rewrite using `[h2, mul_one]`. Conclude with `h1`. Establish `hc : Continuous (fun t : ℝ => phi μ x * (Complex.exp (-(t : ℂ) * (‖x‖ : ℂ) ^ 2) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))))` using `by fun_prop`. Establish `hb : Tendsto bn atTop (𝓝 0)` using `tendsto_one_div_add_atTop_nhds_zero_nat`. Use `(hc.tendsto 0).comp hb` as an intermediate fact.

Simplify `this` using `[Function.comp_def]`.
-/
lemma tendsto_smoothed (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume)
    (y : V) :
    Tendsto (fun n : ℕ => ((∫ z, ker (bn n) (z - y) ∂μ : ℝ) : ℂ)) atTop (𝓝 (dens μ y)) := by
  simp_rw [← smoothed_eq μ (bn_pos _) y]
  unfold dens
  have hcp := continuous_phi μ
  refine tendsto_integral_of_dominated_convergence (fun x => ‖phi μ x‖) (fun n => ?_) hφ.norm
    (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · rw [norm_mul, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    have h2 : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have h1 : ‖Complex.exp (-(bn n : ℂ) * (‖x‖ : ℂ) ^ 2)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      have := (bn_pos n).le
      simp only [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      nlinarith [sq_nonneg ‖x‖]
    rw [h2, mul_one]
    exact h1
  · have hc : Continuous (fun t : ℝ => phi μ x * (Complex.exp (-(t : ℂ) * (‖x‖ : ℂ) ^ 2) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ)))) := by
      fun_prop
    have hb : Tendsto bn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have := (hc.tendsto 0).comp hb
    simpa [Function.comp_def] using this

/- English proof (translation)
Establish `t` using `(Complex.continuous_im.tendsto _).comp (tendsto_smoothed μ hφ y)`. Use `tendsto_nhds_unique t ?_` and prove the remaining obligations. Simplify using `[Function.comp_def]`.
-/
lemma dens_im (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume) (y : V) :
    (dens μ y).im = 0 := by
  have t := (Complex.continuous_im.tendsto _).comp (tendsto_smoothed μ hφ y)
  refine tendsto_nhds_unique t ?_
  simp [Function.comp_def]

/- English proof (translation)
Establish `t` using `(Complex.continuous_re.tendsto _).comp (tendsto_smoothed μ hφ y)`. Use `ge_of_tendsto' t fun n => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Complex.ofReal_re]`. Conclude with `integral_nonneg fun z => ker_nonneg (bn_pos n) _`.
-/
lemma dens_re_nonneg (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume) (y : V) :
    0 ≤ (dens μ y).re := by
  have t := (Complex.continuous_re.tendsto _).comp (tendsto_smoothed μ hφ y)
  refine ge_of_tendsto' t fun n => ?_
  simp only [Function.comp_apply, Complex.ofReal_re]
  exact integral_nonneg fun z => ker_nonneg (bn_pos n) _

/- English proof (translation)
Use `Integrable.of_bound (C := (Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2)) ?_ (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Conclude with `((continuous_ker b).comp (by fun_prop)).aestronglyMeasurable`. Rewrite using `[Real.norm_of_nonneg (ker_nonneg hb _)]`. Conclude with `ker_le hb _`.
-/
lemma integrable_ker_shift (μ : Measure V) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) (y : V) :
    Integrable (fun z => ker b (z - y)) μ := by
  refine Integrable.of_bound (C := (Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2)) ?_
    (Eventually.of_forall fun z => ?_)
  · exact ((continuous_ker b).comp (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (ker_nonneg hb _)]
    exact ker_le hb _

/- English proof (translation)
Establish `h1 : ∀ y : V, ENNReal.ofReal (∫ z, ker b (z - y) ∂μ) = ∫⁻ z, ENNReal.ofReal (ker b (z - y)) ∂μ` using `fun y => ofReal_integral_eq_lintegral_ofReal (integrable_ker_shift μ hb y) (Eventually.of_forall fun z => ker_nonneg hb _)`. Repeatedly rewrite using `[h1]`. Rewrite using `[lintegral_lintegral_swap]`. Establish `h2 : ∀ z : V, ∫⁻ y, ENNReal.ofReal (ker b (z - y)) = 1`. Introduce `z`.

Rewrite using `[← ofReal_integral_eq_lintegral_ofReal ((integrable_ker hb).comp_sub_left z) (Eventually.of_forall fun y => ker_nonneg hb _), integral_sub_left_eq_self (ker b) volume z, integral_ker hb, ENNReal.ofReal_one]`. Repeatedly rewrite using `[h2]`. Simplify using the standard rewrite rules. Establish `hc : Continuous (fun p : V × V => ker b (p.2 - p.1))` using `(continuous_ker b).comp (by fun_prop)`. Conclude with `(ENNReal.continuous_ofReal.comp hc).aemeasurable`.
-/
lemma lintegral_smoothed (μ : Measure V) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) :
    ∫⁻ y, ENNReal.ofReal (∫ z, ker b (z - y) ∂μ) = μ Set.univ := by
  have h1 : ∀ y : V, ENNReal.ofReal (∫ z, ker b (z - y) ∂μ) =
      ∫⁻ z, ENNReal.ofReal (ker b (z - y)) ∂μ := fun y =>
    ofReal_integral_eq_lintegral_ofReal (integrable_ker_shift μ hb y)
      (Eventually.of_forall fun z => ker_nonneg hb _)
  simp_rw [h1]
  rw [lintegral_lintegral_swap]
  · have h2 : ∀ z : V, ∫⁻ y, ENNReal.ofReal (ker b (z - y)) = 1 := by
      intro z
      rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_ker hb).comp_sub_left z)
        (Eventually.of_forall fun y => ker_nonneg hb _),
        integral_sub_left_eq_self (ker b) volume z, integral_ker hb, ENNReal.ofReal_one]
    simp_rw [h2]
    simp
  · have hc : Continuous (fun p : V × V => ker b (p.2 - p.1)) :=
      (continuous_ker b).comp (by fun_prop)
    exact (ENNReal.continuous_ofReal.comp hc).aemeasurable

/- English proof (translation)
Use `set a : ℕ → V → ℝ≥0∞ := fun n y => ENNReal.ofReal (∫ z, ker (bn n) (z - y) ∂μ) with ha`. Establish `hlim : ∀ y, ENNReal.ofReal (dens μ y).re = liminf (fun n => a n y) atTop`. Introduce `y`. Establish `t` using `(Complex.continuous_re.tendsto _).comp (tendsto_smoothed μ hφ y)`. Establish `t2` using `(ENNReal.continuous_ofReal.tendsto _).comp t`.

Use `(Tendsto.liminf_eq ?_).symm` and prove the remaining obligations. Simplify `t2` using `[Function.comp_def, ha]`. Establish `hmeas : ∀ n, Measurable (a n)`. Introduce `n`. Establish `hs : StronglyMeasurable (fun p : V × V => ker (bn n) (p.2 - p.1))` using `((continuous_ker _).comp (by fun_prop)).stronglyMeasurable`.

Conclude with `ENNReal.measurable_ofReal.comp (hs.integral_prod_right' (ν := μ)).measurable`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [ha, lintegral_smoothed μ (bn_pos _)]`. Simplify using the standard rewrite rules.
-/
lemma lintegral_dens_le (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume) :
    ∫⁻ y, ENNReal.ofReal (dens μ y).re ≤ μ Set.univ := by
  set a : ℕ → V → ℝ≥0∞ := fun n y => ENNReal.ofReal (∫ z, ker (bn n) (z - y) ∂μ) with ha
  have hlim : ∀ y, ENNReal.ofReal (dens μ y).re = liminf (fun n => a n y) atTop := by
    intro y
    have t := (Complex.continuous_re.tendsto _).comp (tendsto_smoothed μ hφ y)
    have t2 := (ENNReal.continuous_ofReal.tendsto _).comp t
    refine (Tendsto.liminf_eq ?_).symm
    simpa [Function.comp_def, ha] using t2
  have hmeas : ∀ n, Measurable (a n) := by
    intro n
    have hs : StronglyMeasurable (fun p : V × V => ker (bn n) (p.2 - p.1)) :=
      ((continuous_ker _).comp (by fun_prop)).stronglyMeasurable
    exact ENNReal.measurable_ofReal.comp (hs.integral_prod_right' (ν := μ)).measurable
  calc ∫⁻ y, ENNReal.ofReal (dens μ y).re = ∫⁻ y, liminf (fun n => a n y) atTop :=
        lintegral_congr hlim
    _ ≤ liminf (fun n => ∫⁻ y, a n y) atTop := lintegral_liminf_le hmeas
    _ = μ Set.univ := by
        simp only [ha, lintegral_smoothed μ (bn_pos _)]
        simp

/- English proof (translation)
Establish `hcF : Continuous (𝓕 (phi μ))` using `VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hφ`. Establish `hdF : dens μ = 𝓕 (phi μ)` using `funext (dens_eq_fourier μ)`. Establish `hcd : Continuous (dens μ)` using `hdF ▸ hcF`. Establish `hof : ∀ y, ((dens μ y).re : ℂ) = dens μ y` using `fun y => Complex.ext (by simp) (by simp [dens_im μ hφ y])`. Establish `hcD : Continuous (fun y => (dens μ y).re)` using `Complex.continuous_re.comp hcd`.

Establish `hfin : ∫⁻ y, ENNReal.ofReal (dens μ y).re < ∞` using `(lintegral_dens_le μ hφ).trans_lt (measure_lt_top μ _)`. Establish `hDi : Integrable (fun y => (dens μ y).re) volume` using `⟨hcD.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => dens_re_nonneg μ hφ y)).2 hfin⟩`. Establish `hFi : Integrable (𝓕 (phi μ)) volume`. Rewrite using `[← hdF]`. Conclude with `hDi.ofReal.congr (Eventually.of_forall hof)`.

Establish `hinv : 𝓕⁻ (𝓕 (phi μ)) = phi μ` using `(continuous_phi μ).fourierInv_fourier_eq hφ hFi`. Use `⟨fun y => (dens μ y).re, hcD, dens_re_nonneg μ hφ, hof, ?_⟩` and prove the remaining obligations. Use `set ν := (volume : Measure V).withDensity (fun y => ENNReal.ofReal (dens μ y).re) with hν`. Use `haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfin.ne`. Use `Measure.ext_of_charFun (funext fun t => ?_)` and prove the remaining obligations.

Establish `hpi : (2 * Real.pi) ≠ 0` using `by positivity`. Establish `h1 : charFun μ t = phi μ ((2 * Real.pi)⁻¹ • t)`. Rewrite using `[phi_eq_charFun, smul_smul, mul_inv_cancel₀ hpi, one_smul]`. Rewrite using `[h1, ← hinv, Real.fourierInv_eq', charFun_apply, hν, integral_withDensity_eq_integral_toReal_smul (show Measurable (fun y => ENNReal.ofReal (dens μ y).re) from ENNReal.measurable_ofReal.comp hcD.measurable) (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]`. Use `integral_congr_ae (Eventually.of_forall fun v => ?_)` and prove the remaining obligations.

Simplify using `only [Function.comp_apply]`. Rewrite using `[ENNReal.toReal_ofReal (dens_re_nonneg μ hφ v), ← hdF, ← hof v, inner_smul_right, Complex.real_smul]`. Simplify using `only [smul_eq_mul, Complex.ofReal_re]`. Rewrite using `[mul_comm, mul_inv_cancel_left₀ hpi]`.
-/
theorem exists_density (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume) :
    ∃ D : V → ℝ, Continuous D ∧ (∀ y, 0 ≤ D y) ∧ (∀ y, (D y : ℂ) = dens μ y) ∧
      μ = (volume : Measure V).withDensity (fun y => ENNReal.ofReal (D y)) := by
  have hcF : Continuous (𝓕 (phi μ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hφ
  have hdF : dens μ = 𝓕 (phi μ) := funext (dens_eq_fourier μ)
  have hcd : Continuous (dens μ) := hdF ▸ hcF
  have hof : ∀ y, ((dens μ y).re : ℂ) = dens μ y := fun y =>
    Complex.ext (by simp) (by simp [dens_im μ hφ y])
  have hcD : Continuous (fun y => (dens μ y).re) := Complex.continuous_re.comp hcd
  have hfin : ∫⁻ y, ENNReal.ofReal (dens μ y).re < ∞ :=
    (lintegral_dens_le μ hφ).trans_lt (measure_lt_top μ _)
  have hDi : Integrable (fun y => (dens μ y).re) volume :=
    ⟨hcD.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun y => dens_re_nonneg μ hφ y)).2 hfin⟩
  have hFi : Integrable (𝓕 (phi μ)) volume := by
    rw [← hdF]
    exact hDi.ofReal.congr (Eventually.of_forall hof)
  have hinv : 𝓕⁻ (𝓕 (phi μ)) = phi μ := (continuous_phi μ).fourierInv_fourier_eq hφ hFi
  refine ⟨fun y => (dens μ y).re, hcD, dens_re_nonneg μ hφ, hof, ?_⟩
  set ν := (volume : Measure V).withDensity (fun y => ENNReal.ofReal (dens μ y).re) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfin.ne
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h1 : charFun μ t = phi μ ((2 * Real.pi)⁻¹ • t) := by
    rw [phi_eq_charFun, smul_smul, mul_inv_cancel₀ hpi, one_smul]
  rw [h1, ← hinv, Real.fourierInv_eq', charFun_apply, hν,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun y => ENNReal.ofReal (dens μ y).re) from
        ENNReal.measurable_ofReal.comp hcD.measurable)
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (dens_re_nonneg μ hφ v), ← hdF, ← hof v, inner_smul_right,
    Complex.real_smul]
  simp only [smul_eq_mul, Complex.ofReal_re]
  rw [mul_comm, mul_inv_cancel_left₀ hpi]

/- English proof (translation)
Introduce `κ _ m _ hint`. Set `e : (κ → ℝ) ≃ᵐ EuclideanSpace ℝ κ` to `MeasurableEquiv.toLp 2 _`. Establish `hmp : MeasurePreserving e volume volume` using `PiLp.volume_preserving_toLp κ`. Use `set μ : Measure (EuclideanSpace ℝ κ) := m.map e with hμ`. Use `haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance`.

Establish `hin : ∀ z x : κ → ℝ, inner ℝ (e z) (e x) = ∑ w, z w * x w`. Introduce `z x`. Simplify using `only [e, MeasurableEquiv.toLp_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]`. Conclude with `Finset.sum_congr rfl fun w _ => mul_comm _ _`. Establish `hphi : ∀ x : κ → ℝ, phi μ (e x) = ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m`.

Introduce `x`. Unfold `phi`. Rewrite using `[hμ, integral_map_equiv]`. Repeatedly rewrite using `[hin]`. Establish `hφ : Integrable (phi μ) volume`.

Rewrite using `[← hmp.integrable_comp_emb e.measurableEmbedding]`. Conclude with `hint.congr (Eventually.of_forall fun x => (hphi x).symm)`. Take `⟨D, hc, h0, hD, hm⟩` from `exists_density μ hφ`. Use `⟨D ∘ e, hc.comp (PiLp.continuous_toLp 2 _), fun y => h0 _, fun y => ?_, fun U hU => ?_⟩` and prove the remaining obligations. Rewrite using `[Function.comp_apply, hD]`.

Unfold `dens`. Rewrite using `[← hmp.integral_comp e.measurableEmbedding]`. Repeatedly rewrite using `[hphi, hin]`. Establish `h1 : m U = μ (e.symm ⁻¹' U)`. Rewrite using `[hμ, e.map_apply, ← Set.preimage_comp]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, hm, withDensity_apply _ (e.symm.measurable hU), ← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding]`. Simplify using `[Function.comp_def, ← Set.preimage_comp]`.
-/
theorem density_of_integrable_charFun :
    ∀ (κ : Type) [Fintype κ] (m : Measure (κ → ℝ)), IsFiniteMeasure m → Integrable (fun x : κ → ℝ => ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m) → ∃ D : (κ → ℝ) → ℝ, Continuous D ∧ (∀ y, 0 ≤ D y) ∧ (∀ y, (D y : ℂ) = ∫ x : κ → ℝ, (∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, y w * x w : ℝ) : ℂ))) ∧ ∀ U : Set (κ → ℝ), MeasurableSet U → m U = ∫⁻ y in U, ENNReal.ofReal (D y) := by
  intro κ _ m _ hint
  let e : (κ → ℝ) ≃ᵐ EuclideanSpace ℝ κ := MeasurableEquiv.toLp 2 _
  have hmp : MeasurePreserving e volume volume := PiLp.volume_preserving_toLp κ
  set μ : Measure (EuclideanSpace ℝ κ) := m.map e with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hin : ∀ z x : κ → ℝ, inner ℝ (e z) (e x) = ∑ w, z w * x w := by
    intro z x
    simp only [e, MeasurableEquiv.toLp_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have hphi : ∀ x : κ → ℝ, phi μ (e x) =
      ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m := by
    intro x
    unfold phi
    rw [hμ, integral_map_equiv]
    simp_rw [hin]
  have hφ : Integrable (phi μ) volume := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]
    exact hint.congr (Eventually.of_forall fun x => (hphi x).symm)
  obtain ⟨D, hc, h0, hD, hm⟩ := exists_density μ hφ
  refine ⟨D ∘ e, hc.comp (PiLp.continuous_toLp 2 _), fun y => h0 _, fun y => ?_, fun U hU => ?_⟩
  · rw [Function.comp_apply, hD]
    unfold dens
    rw [← hmp.integral_comp e.measurableEmbedding]
    simp_rw [hphi, hin]
  · have h1 : m U = μ (e.symm ⁻¹' U) := by
      rw [hμ, e.map_apply, ← Set.preimage_comp]
      simp
    rw [h1, hm, withDensity_apply _ (e.symm.measurable hU),
      ← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding]
    simp [Function.comp_def, ← Set.preimage_comp]

end GlobalTheory.CompanionTheory.SW.CharDensity
