import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.SobolevMollifier

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Translation

open Complex in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[iteratedDeriv_succ, ih]`. Use function extensionality and compare the values at `t`.

Establish `h` using `(((hasDerivAt_id t).ofReal_comp.const_mul I).cexp).const_mul (I ^ n)`. Simplify using `only [id] at h`. Rewrite using `[h.deriv]`. Simplify using `only [Complex.ofReal_one, mul_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iteratedDeriv_cexp_I_mul (n : ℕ) :
    iteratedDeriv n (fun t : ℝ ↦ exp (I * t)) = fun t : ℝ ↦ I ^ n * exp (I * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h := (((hasDerivAt_id t).ofReal_comp.const_mul I).cexp).const_mul (I ^ n)
    simp only [id] at h
    rw [h.deriv]
    simp only [Complex.ofReal_one, mul_one]
    ring

open Complex in
/- English proof (translation)
Use `⟨Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff), fun n ↦ ⟨0, 1, fun t ↦ ?_⟩⟩` and prove the remaining obligations. Rewrite using `[norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_I_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]`. Simplify using the standard rewrite rules.
-/
theorem hasTemperateGrowth_cexp_I_mul : (fun t : ℝ ↦ exp (I * t)).HasTemperateGrowth := by
  refine ⟨Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff),
    fun n ↦ ⟨0, 1, fun t ↦ ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_I_mul, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]
  simp

def expChar (a : E) (ξ : E) : ℂ := Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ ξ a : ℝ) : ℂ))

/- English proof (translation)
Establish `hL : (fun ξ : E ↦ 2 * Real.pi * inner ℝ ξ a).HasTemperateGrowth`. Establish `: (fun ξ : E ↦ 2 * Real.pi * inner ℝ ξ a) = ⇑((2 * Real.pi) • innerSL ℝ a)`. Use function extensionality and compare the values at `ξ`. Simplify using `[real_inner_comm]`. Rewrite using `[this]`.

Conclude with `ContinuousLinearMap.hasTemperateGrowth _`. Conclude with `hasTemperateGrowth_cexp_I_mul.comp hL`.
-/
theorem expChar_hasTemperateGrowth (a : E) : (expChar a : E → ℂ).HasTemperateGrowth := by
  have hL : (fun ξ : E ↦ 2 * Real.pi * inner ℝ ξ a).HasTemperateGrowth := by
    have : (fun ξ : E ↦ 2 * Real.pi * inner ℝ ξ a) = ⇑((2 * Real.pi) • innerSL ℝ a) := by
      funext ξ; simp [real_inner_comm]
    rw [this]; exact ContinuousLinearMap.hasTemperateGrowth _
  exact hasTemperateGrowth_cexp_I_mul.comp hL

/- English proof (translation)
The claim follows from `Complex.norm_exp_I_mul_ofReal _`.
-/
theorem norm_expChar (a ξ : E) : ‖expChar a ξ‖ = 1 := Complex.norm_exp_I_mul_ofReal _

/- English proof (translation)
Rewrite using `[expChar, Real.fourierChar_apply, mul_comm]`.
-/
theorem expChar_eq_fourierChar (a ξ : E) : expChar a ξ = (𝐞 (inner ℝ ξ a) : ℂ) := by
  rw [expChar, Real.fourierChar_apply, mul_comm]

variable (F) in

def translate (h : E) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.compSubConstCLM ℂ (-h))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem translate_apply_apply (h : E) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    translate F h u φ = u (SchwartzMap.compSubConstCLM ℂ (-h) φ) := rfl

/- English proof (translation)
Apply `SchwartzMap.ext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, SchwartzMap.fourier_coe, Real.fourier_eq]`. Establish `key : ∀ ξ : E, 𝐞 (-inner ℝ ξ x) • SchwartzMap.smulLeftCLM ℂ (expChar (-h)) (𝓕⁻ φ) ξ = 𝐞 (-inner ℝ ξ (x + h)) • (𝓕⁻ φ : 𝓢(E, ℂ)) ξ`. Introduce `ξ`.

Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply (expChar_hasTemperateGrowth _), expChar_eq_fourierChar, Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, inner_add_right, inner_neg_right]`. Use `congr 3`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[key]`. Rewrite using `[← Real.fourier_eq, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]`.
-/
theorem fourier_expChar_smul_fourierInv (h : E) (φ : 𝓢(E, ℂ)) :
    𝓕 (SchwartzMap.smulLeftCLM ℂ (expChar (-h)) (𝓕⁻ φ)) = SchwartzMap.compSubConstCLM ℂ (-h) φ := by
  apply SchwartzMap.ext; intro x
  rw [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, SchwartzMap.fourier_coe, Real.fourier_eq]
  have key : ∀ ξ : E, 𝐞 (-inner ℝ ξ x) • SchwartzMap.smulLeftCLM ℂ (expChar (-h)) (𝓕⁻ φ) ξ =
      𝐞 (-inner ℝ ξ (x + h)) • (𝓕⁻ φ : 𝓢(E, ℂ)) ξ := by
    intro ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply (expChar_hasTemperateGrowth _), expChar_eq_fourierChar,
      Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← Circle.coe_mul, ← AddChar.map_add_eq_mul, inner_add_right, inner_neg_right]
    congr 3; ring
  simp_rw [key]
  rw [← Real.fourier_eq, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]

/- English proof (translation)
Use extensionality with `φ`. Rewrite using `[translate_apply_apply, fourierMultiplierCLM_apply_apply, fourier_expChar_smul_fourierInv]`.
-/
theorem translate_eq_fourierMultiplierCLM (h : E) (u : 𝓢'(E, F)) :
    translate F h u = fourierMultiplierCLM F (expChar (-h)) u := by
  ext φ
  rw [translate_apply_apply, fourierMultiplierCLM_apply_apply, fourier_expChar_smul_fourierInv]

/- English proof (translation)
Rewrite using `[translate_apply_apply, Lp.toTemperedDistribution_apply]`. Use `(measurePreserving_add_right (volume : Measure E) h).integral_comp (measurableEmbedding_addRight h) (fun x ↦ φ x • f (x - h))` as an intermediate fact. Simplify using `only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add] at this ⊢`. Rewrite using `[← this]`. Use `congr 1`.

Use extensionality with `x`. Rewrite using `[add_sub_cancel_right]`.
-/
theorem translate_toTemperedDistribution (h : E) (f : Lp F 2 (volume : Measure E)) (φ : 𝓢(E, ℂ)) :
    translate F h (f : 𝓢'(E, F)) φ = ∫ x, φ x • f (x - h) := by
  rw [translate_apply_apply, Lp.toTemperedDistribution_apply]
  have := (measurePreserving_add_right (volume : Measure E) h).integral_comp
    (measurableEmbedding_addRight h) (fun x ↦ φ x • f (x - h))
  simp only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add] at this ⊢
  rw [← this]
  congr 1; ext x
  rw [add_sub_cancel_right]

end Translation

/- English proof (translation)
Establish `hc : Continuous (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ s)` using `(continuous_const.add (continuous_norm.pow 2)).rpow_const fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'`. Conclude with `((hc.mul hg).aestronglyMeasurable).mul ((fourierFun_aestronglyMeasurable u).norm.pow 2)`.
-/
theorem aestronglyMeasurable_weight_mul_sq {s : ℝ} (u : SobolevSpace E F s) (g : E → ℝ)
    (hg : Continuous g) :
    AEStronglyMeasurable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s * g ξ * ‖fourierFun u ξ‖ ^ 2)
      (volume : Measure E) := by
  have hc : Continuous (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ s) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
  exact ((hc.mul hg).aestronglyMeasurable).mul ((fourierFun_aestronglyMeasurable u).norm.pow 2)

/- English proof (translation)
Rewrite using `[memSobolev_iff_fourier]`. Use `⟨fourierFun u, ?_, fourier_apply_eq_integral u⟩` and prove the remaining obligations. Use `set b := stdOrthonormalBasis ℝ E`. Establish `hmeas : AEStronglyMeasurable (fun ξ ↦ weight (s + 1) ξ • fourierFun u ξ) (volume : Measure E)` using `(weight_hasTemperateGrowth (s + 1)).1.continuous.aestronglyMeasurable.smul (fourierFun_aestronglyMeasurable u)`. Rewrite using `[memLp_two_iff_integrable_sq_norm hmeas]`.

Use `⟨hmeas.norm.pow 2, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ by positivity)]`. Establish `hpt : ∀ ξ, ENNReal.ofReal (‖weight (s + 1) ξ • fourierFun u ξ‖ ^ 2) = ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * 1 * ‖fourierFun u ξ‖ ^ 2) + ∑ i, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ (b i) ^ 2 * ‖fourierFun u ξ‖ ^ 2)`. Introduce `ξ`. Establish `h0 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2` using `by positivity`.

Rewrite using `[← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by positivity), ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ ↦ by positivity)]`. Use `congr 1`. Establish `hsum : ∑ i, (1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ (b i) ^ 2 * ‖fourierFun u ξ‖ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ s * ‖ξ‖ ^ 2 * ‖fourierFun u ξ‖ ^ 2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`.

Use `_ = _ := by rw [b.sum_sq_inner_left ξ]`. Establish `hw : ((1 + ‖ξ‖ ^ 2) ^ ((s + 1) / 2)) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ s * (1 + ‖ξ‖ ^ 2)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul h0.le, ← Real.rpow_add_one h0.ne']`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum, norm_smul, norm_weight, mul_pow, hw]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hpt]`. Establish `hm : ∀ g : E → ℝ, Continuous g → AEMeasurable (fun ξ ↦ ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * g ξ * ‖fourierFun u ξ‖ ^ 2)) (volume : Measure E)` using `fun g hg ↦ (aestronglyMeasurable_weight_mul_sq u g hg).aemeasurable.ennreal_ofReal`.

Rewrite using `[lintegral_add_left' (hm _ continuous_const), lintegral_finsetSum' _ fun i _ ↦ hm (fun ξ ↦ inner ℝ ξ (b i) ^ 2) (by fun_prop)]`. Use `ENNReal.add_lt_top.2 ⟨?_, ENNReal.sum_lt_top.2 fun i _ ↦ h (b i)⟩` and prove the remaining obligations. Use `(integrable_weight_mul_norm_sq_fourierFun u).lintegral_lt_top` as an intermediate fact. Simplify using `using this`.
-/
theorem memSobolev_add_one_of_lintegral {s : ℝ} (u : SobolevSpace E F s)
    (h : ∀ v : E, ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ v ^ 2 *
      ‖fourierFun u ξ‖ ^ 2) < ⊤) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) := by
  rw [memSobolev_iff_fourier]
  refine ⟨fourierFun u, ?_, fourier_apply_eq_integral u⟩
  set b := stdOrthonormalBasis ℝ E
  have hmeas : AEStronglyMeasurable (fun ξ ↦ weight (s + 1) ξ • fourierFun u ξ)
      (volume : Measure E) :=
    (weight_hasTemperateGrowth (s + 1)).1.continuous.aestronglyMeasurable.smul
      (fourierFun_aestronglyMeasurable u)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine ⟨hmeas.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ by positivity)]
  have hpt : ∀ ξ, ENNReal.ofReal (‖weight (s + 1) ξ • fourierFun u ξ‖ ^ 2) =
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * 1 * ‖fourierFun u ξ‖ ^ 2) +
        ∑ i, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ (b i) ^ 2 * ‖fourierFun u ξ‖ ^ 2) := by
    intro ξ
    have h0 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by positivity),
      ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ ↦ by positivity)]
    congr 1
    have hsum : ∑ i, (1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ (b i) ^ 2 * ‖fourierFun u ξ‖ ^ 2 =
        (1 + ‖ξ‖ ^ 2) ^ s * ‖ξ‖ ^ 2 * ‖fourierFun u ξ‖ ^ 2 := by
      calc ∑ i, (1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ (b i) ^ 2 * ‖fourierFun u ξ‖ ^ 2
          = (1 + ‖ξ‖ ^ 2) ^ s * (∑ i, inner ℝ ξ (b i) ^ 2) * ‖fourierFun u ξ‖ ^ 2 := by
            rw [Finset.mul_sum, Finset.sum_mul]
        _ = _ := by rw [b.sum_sq_inner_left ξ]
    have hw : ((1 + ‖ξ‖ ^ 2) ^ ((s + 1) / 2)) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ s * (1 + ‖ξ‖ ^ 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, ← Real.rpow_add_one h0.ne']
      congr 1; push_cast; ring
    rw [hsum, norm_smul, norm_weight, mul_pow, hw]
    ring
  simp_rw [hpt]
  have hm : ∀ g : E → ℝ, Continuous g → AEMeasurable (fun ξ ↦ ENNReal.ofReal
      ((1 + ‖ξ‖ ^ 2) ^ s * g ξ * ‖fourierFun u ξ‖ ^ 2)) (volume : Measure E) :=
    fun g hg ↦ (aestronglyMeasurable_weight_mul_sq u g hg).aemeasurable.ennreal_ofReal
  rw [lintegral_add_left' (hm _ continuous_const),
    lintegral_finsetSum' _ fun i _ ↦ hm (fun ξ ↦ inner ℝ ξ (b i) ^ 2) (by fun_prop)]
  refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.sum_lt_top.2 fun i _ ↦ h (b i)⟩
  have := (integrable_weight_mul_norm_sq_fourierFun u).lintegral_lt_top
  simpa using this

/- English proof (translation)
Establish `hG` using `(Lp.memLp (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E))).locallyIntegrable (by norm_num)`. Use `hG.continuous_smul (weight_hasTemperateGrowth (-s)).1.continuous` as an intermediate fact. Conclude with `this`.
-/
theorem locallyIntegrable_fourierFun {s : ℝ} (u : SobolevSpace E F s) :
    LocallyIntegrable (fourierFun u) (volume : Measure E) := by
  have hG := (Lp.memLp (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E))).locallyIntegrable
    (by norm_num)
  have := hG.continuous_smul (weight_hasTemperateGrowth (-s)).1.continuous
  exact this

open LineDeriv in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hu v`. Use `SobolevSpace.memSobolev_toDistribution (SobolevSpace.lineDerivCLM v (SobolevSpace.mk (s := s + 1) _ hu))` as an intermediate fact. Rewrite `this` using `[SobolevSpace.toDistribution_lineDerivCLM, SobolevSpace.toDistribution_mk, add_sub_cancel_right]`. Then use the resulting hypothesis. Introduce `hv`.

Apply `memSobolev_add_one_of_lintegral` to reduce the goal to its premises. Introduce `v`. Use `set w : SobolevSpace E F s := SobolevSpace.mk _ (hv v)`. Use `set d := SobolevSpace.lineDerivCLM (s := s) v u`. Establish `hd` using `(fourierFun_multiplier (m := fun ξ ↦ (2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) (by fun_prop) (SobolevSpace.lineDeriv_bound v) u).1`.

Establish `hwd : fourierFun w =ᵐ[volume] fourierFun d`. Apply `ae_eq_of_integral_schwartz_smul_eq (locallyIntegrable_fourierFun w) (locallyIntegrable_fourierFun d)` to reduce the goal to its premises. Introduce `φ _`. Rewrite using `[← fourier_apply_eq_integral, ← fourier_apply_eq_integral]`. Simplify using `[w, d]`.

Establish `hint` using `(integrable_weight_mul_norm_sq_fourierFun w).lintegral_lt_top`. Establish `hc : (0 : ℝ) < (2 * Real.pi) ^ 2` using `by positivity`. Establish `hpt : ∀ᵐ ξ ∂(volume : Measure E), ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ v ^ 2 * ‖fourierFun u ξ‖ ^ 2) = ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun w ξ‖ ^ 2)` using `by filter_upwards [hwd, hd] with ξ h1 h2`. Rewrite using `[← ENNReal.ofReal_mul (by positivity), h1]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `_ = _ * ((1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun (SobolevSpace.multiplier _ _ u) ξ‖ ^ 2)`. Establish `h2pi : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi`. Rewrite using `[norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]`. Rewrite using `[h2, norm_smul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, h2pi, Real.norm_eq_abs, mul_one, mul_pow, mul_pow, mul_pow, sq_abs]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[lintegral_congr_ae hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Conclude with `ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint`.
-/
theorem memSobolev_add_one_iff_lineDeriv {s : ℝ} (u : SobolevSpace E F s) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) ↔
      ∀ v : E, MemSobolev s 2 (∂_{v} (SobolevSpace.toDistribution u)) := by
  constructor
  · intro hu v
    have := SobolevSpace.memSobolev_toDistribution
      (SobolevSpace.lineDerivCLM v (SobolevSpace.mk (s := s + 1) _ hu))
    rwa [SobolevSpace.toDistribution_lineDerivCLM, SobolevSpace.toDistribution_mk,
      add_sub_cancel_right] at this
  · intro hv
    apply memSobolev_add_one_of_lintegral
    intro v
    set w : SobolevSpace E F s := SobolevSpace.mk _ (hv v)
    set d := SobolevSpace.lineDerivCLM (s := s) v u
    have hd := (fourierFun_multiplier (m := fun ξ ↦ (2 * Real.pi * Complex.I) *
      ((inner ℝ ξ v : ℝ) : ℂ)) (by fun_prop) (SobolevSpace.lineDeriv_bound v) u).1
    have hwd : fourierFun w =ᵐ[volume] fourierFun d := by
      apply ae_eq_of_integral_schwartz_smul_eq (locallyIntegrable_fourierFun w)
        (locallyIntegrable_fourierFun d)
      intro φ _
      rw [← fourier_apply_eq_integral, ← fourier_apply_eq_integral]
      simp [w, d]
    have hint := (integrable_weight_mul_norm_sq_fourierFun w).lintegral_lt_top
    have hc : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
    have hpt : ∀ᵐ ξ ∂(volume : Measure E),
        ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ v ^ 2 * ‖fourierFun u ξ‖ ^ 2) =
          ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) *
            ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun w ξ‖ ^ 2) := by
      filter_upwards [hwd, hd] with ξ h1 h2
      rw [← ENNReal.ofReal_mul (by positivity), h1]
      congr 1
      change _ = _ * ((1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun (SobolevSpace.multiplier _ _ u) ξ‖ ^ 2)
      have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
        rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [h2, norm_smul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, h2pi,
        Real.norm_eq_abs, mul_one, mul_pow, mul_pow, mul_pow, sq_abs]
      field_simp
    rw [lintegral_congr_ae hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

def dqSymbol (v : E) (t : ℝ) (ξ : E) : ℂ := ((t⁻¹ : ℝ) : ℂ) * (expChar (t • v) ξ - 1)

/- English proof (translation)
The claim follows from `(Function.HasTemperateGrowth.const _).mul ((expChar_hasTemperateGrowth _).sub (Function.HasTemperateGrowth.const 1))`.
-/
theorem dqSymbol_hasTemperateGrowth (v : E) (t : ℝ) : (dqSymbol v t : E → ℂ).HasTemperateGrowth :=
  (Function.HasTemperateGrowth.const _).mul
    ((expChar_hasTemperateGrowth _).sub (Function.HasTemperateGrowth.const 1))

/- English proof (translation)
Rewrite using `[expChar]`. Use `Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]`.
-/
theorem norm_expChar_sub_one_le (a ξ : E) :
    ‖expChar a ξ - 1‖ ≤ 2 * Real.pi * |inner ℝ ξ a| := by
  rw [expChar]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

/- English proof (translation)
Rewrite using `[dqSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Break down `eq_or_ne t 0 with rfl | ht` into its components or cases. Simplify using the standard rewrite rules. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[inner_smul_right, abs_mul, abs_inv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem norm_dqSymbol_le (v : E) (t : ℝ) (ξ : E) : ‖dqSymbol v t ξ‖ ≤ 2 * Real.pi * |inner ℝ ξ v| := by
  rw [dqSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rcases eq_or_ne t 0 with rfl | ht
  · simp; positivity
  calc |t⁻¹| * ‖expChar (t • v) ξ - 1‖ ≤ |t⁻¹| * (2 * Real.pi * |inner ℝ ξ (t • v)|) := by
        gcongr; exact norm_expChar_sub_one_le _ _
    _ = 2 * Real.pi * |inner ℝ ξ v| := by
        rw [inner_smul_right, abs_mul, abs_inv]
        field_simp

/- English proof (translation)
Rewrite using `[dqSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, mul_comm]`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_dqSymbol_le' (v : E) (t : ℝ) (ξ : E) : ‖dqSymbol v t ξ‖ ≤ 2 * |t|⁻¹ := by
  rw [dqSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, mul_comm]
  gcongr
  calc ‖expChar (t • v) ξ - 1‖ ≤ ‖expChar (t • v) ξ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_expChar, norm_one]; norm_num

/- English proof (translation)
Use `(norm_dqSymbol_le v t ξ).trans ?_` and prove the remaining obligations. Rewrite using `[show (s + 1 - s) / 2 = 1 / 2 by ring, ← Real.sqrt_eq_rpow]`. Establish `h : |inner ℝ ξ v| ≤ ‖v‖ * √(1 + ‖ξ‖ ^ 2)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Real.le_sqrt_of_sq_le (by linarith)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem dqSymbol_bound {s : ℝ} (v : E) (t : ℝ) (ξ : E) :
    ‖dqSymbol v t ξ‖ ≤ (2 * Real.pi * ‖v‖) * (1 + ‖ξ‖ ^ 2) ^ ((s + 1 - s) / 2) := by
  refine (norm_dqSymbol_le v t ξ).trans ?_
  rw [show (s + 1 - s) / 2 = 1 / 2 by ring, ← Real.sqrt_eq_rpow]
  have h : |inner ℝ ξ v| ≤ ‖v‖ * √(1 + ‖ξ‖ ^ 2) :=
    calc |inner ℝ ξ v| ≤ ‖ξ‖ * ‖v‖ := abs_real_inner_le_norm ξ v
      _ = ‖v‖ * ‖ξ‖ := mul_comm _ _
      _ ≤ ‖v‖ * √(1 + ‖ξ‖ ^ 2) := by
          gcongr
          exact Real.le_sqrt_of_sq_le (by linarith)
  calc 2 * Real.pi * |inner ℝ ξ v| ≤ 2 * Real.pi * (‖v‖ * √(1 + ‖ξ‖ ^ 2)) := by gcongr
    _ = _ := by ring

open Filter Topology in
/- English proof (translation)
Use `set a : ℝ := 2 * Real.pi * inner ℝ ξ v`. Establish `hf : HasDerivAt (fun t : ℝ ↦ Complex.exp (Complex.I * ((t * a : ℝ) : ℂ))) (Complex.I * a) 0`. Use `(((hasDerivAt_id (0 : ℝ)).mul_const a).ofReal_comp.const_mul Complex.I).cexp` as an intermediate fact. Simplify using `using this`. Establish `h` using `hasDerivAt_iff_tendsto_slope_zero.1 hf`.

Establish `e : ∀ t : ℝ, t⁻¹ • (Complex.exp (Complex.I * (((0 + t) * a : ℝ) : ℂ)) - Complex.exp (Complex.I * (((0 : ℝ) * a : ℝ) : ℂ))) = dqSymbol v t ξ`. Introduce `t`. Rewrite using `[dqSymbol, expChar, inner_smul_right, Complex.real_smul, zero_add, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero]`. Simplify using `only [a]`. Use `congr 3`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`. Use `h using 2` and compare the differences between its conclusion and the goal. Simplify using `only [a]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_dqSymbol (v ξ : E) :
    Tendsto (fun t ↦ dqSymbol v t ξ) (𝓝[≠] 0)
      (𝓝 ((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ))) := by
  set a : ℝ := 2 * Real.pi * inner ℝ ξ v
  have hf : HasDerivAt (fun t : ℝ ↦ Complex.exp (Complex.I * ((t * a : ℝ) : ℂ)))
      (Complex.I * a) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const a).ofReal_comp.const_mul Complex.I).cexp
    simpa using this
  have h := hasDerivAt_iff_tendsto_slope_zero.1 hf
  have e : ∀ t : ℝ, t⁻¹ • (Complex.exp (Complex.I * (((0 + t) * a : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (((0 : ℝ) * a : ℝ) : ℂ))) = dqSymbol v t ξ := by
    intro t
    rw [dqSymbol, expChar, inner_smul_right, Complex.real_smul, zero_add, zero_mul,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    simp only [a]
    congr 3
    push_cast
    ring
  simp_rw [e] at h
  convert h using 2
  simp only [a]; push_cast; ring

namespace SobolevSpace

variable {s : ℝ}

def diffQuot (v : E) (t : ℝ) : SobolevSpace E F s →L[ℂ] SobolevSpace E F s :=
  multiplier (dqSymbol_hasTemperateGrowth v t) (bound_of_le (norm_dqSymbol_le' v t))

/- English proof (translation)
Rewrite using `[diffQuot, toDistribution_multiplier, translate_eq_fourierMultiplierCLM, neg_neg]`. Establish `hsub : (dqSymbol v t : E → ℂ) = ((t⁻¹ : ℝ) : ℂ) • (expChar (t • v) - fun _ ↦ (1 : ℂ))`. Use function extensionality and compare the values at `ξ`. Simplify using `[dqSymbol]`. Rewrite using `[hsub, fourierMultiplierCLM_smul ((expChar_hasTemperateGrowth _).sub (Function.HasTemperateGrowth.const 1)), smul_apply]`.

Use `congr 1`. Rewrite using `[fourierMultiplierCLM_apply, fourierMultiplierCLM_apply, smulLeftCLM_sub (expChar_hasTemperateGrowth _) (Function.HasTemperateGrowth.const 1), sub_apply, smulLeftCLM_const, one_smul, ← fourierInvCLM_apply (R := ℂ), map_sub, fourierInvCLM_apply, fourierInvCLM_apply, FourierTransfo …`.
-/
theorem toDistribution_diffQuot (v : E) (t : ℝ) (u : SobolevSpace E F s) :
    toDistribution (diffQuot v t u) =
      ((t⁻¹ : ℝ) : ℂ) • (translate F (-(t • v)) (toDistribution u) - toDistribution u) := by
  rw [diffQuot, toDistribution_multiplier, translate_eq_fourierMultiplierCLM, neg_neg]
  have hsub : (dqSymbol v t : E → ℂ) = ((t⁻¹ : ℝ) : ℂ) • (expChar (t • v) - fun _ ↦ (1 : ℂ)) := by
    funext ξ; simp [dqSymbol]
  rw [hsub, fourierMultiplierCLM_smul ((expChar_hasTemperateGrowth _).sub
    (Function.HasTemperateGrowth.const 1)), smul_apply]
  congr 1
  rw [fourierMultiplierCLM_apply, fourierMultiplierCLM_apply,
    smulLeftCLM_sub (expChar_hasTemperateGrowth _) (Function.HasTemperateGrowth.const 1),
    sub_apply, smulLeftCLM_const, one_smul, ← fourierInvCLM_apply (R := ℂ), map_sub,
    fourierInvCLM_apply, fourierInvCLM_apply, FourierTransform.fourierInv_fourier_eq]

/- English proof (translation)
Establish `h : diffQuot v t (inclusion (le_add_of_nonneg_right zero_le_one) u) = multiplier (dqSymbol_hasTemperateGrowth v t) (dqSymbol_bound (s` using `s) v t) u := by`. Apply `toDistribution_injective` to reduce the goal to its premises. Simplify using `[diffQuot]`. Rewrite using `[h]`. Conclude with `norm_multiplier_apply_le _ _ u`.
-/
theorem norm_diffQuot_le (v : E) (t : ℝ) (u : SobolevSpace E F (s + 1)) :
    ‖diffQuot v t (inclusion (le_add_of_nonneg_right zero_le_one) u)‖ ≤ 2 * Real.pi * ‖v‖ * ‖u‖ := by
  have h : diffQuot v t (inclusion (le_add_of_nonneg_right zero_le_one) u) =
      multiplier (dqSymbol_hasTemperateGrowth v t) (dqSymbol_bound (s := s) v t) u := by
    apply toDistribution_injective
    simp [diffQuot]
  rw [h]
  exact norm_multiplier_apply_le _ _ u

end SobolevSpace

open Filter Topology in

/- English proof (translation)
Apply `memSobolev_add_one_of_lintegral` to reduce the goal to its premises. Introduce `v`. Take `⟨C, hC⟩` from `h v`. Use `set f : ℝ → E → ℝ≥0∞ := fun t ξ ↦ ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖dqSymbol v t ξ • fourierFun u ξ‖ ^ 2)`. Establish `hc : Continuous (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ s)` using `(continuous_const.add (continuous_norm.pow 2)).rpow_const fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'`.

Establish `hfm : ∀ t, AEMeasurable (f t) (volume : Measure E)` using `fun t ↦ (hc.aestronglyMeasurable.mul (((dqSymbol_hasTemperateGrowth v t).1.continuous.aestronglyMeasurable.smul (fourierFun_aestronglyMeasurable u)).norm.pow 2)).aemeasurable.ennreal_ofReal`. Establish `hnorm : ∀ t, ∫⁻ ξ, f t ξ = ENNReal.ofReal (‖SobolevSpace.diffQuot v t u‖ ^ 2)`. Introduce `t`. Establish `hm` using `fourierFun_multiplier (dqSymbol_hasTemperateGrowth v t) (bound_of_le (s := s) (norm_dqSymbol_le' v t)) u`. Express the relevant statement in the definitionally equal form `_ = ENNReal.ofReal (‖SobolevSpace.multiplier _ _ u‖ ^ 2)`.

Rewrite using `[hm.2, ofReal_integral_eq_lintegral_ofReal]`. Establish `hi` using `integrable_weight_mul_norm_sq_fourierFun (SobolevSpace.multiplier (dqSymbol_hasTemperateGrowth v t) (bound_of_le (s := s) (norm_dqSymbol_le' v t)) u)`. Use `hi.congr ?_` and prove the remaining obligations. Use `filter_upwards [hm.1] with ξ hξ`. Rewrite using `[hξ]`.

Conclude with `ae_of_all _ fun ξ ↦ by positivity`. Establish `hlim : ∀ ξ, Tendsto (fun t ↦ f t ξ) (𝓝[≠] 0) (𝓝 (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) • fourierFun u ξ‖ ^ 2)))`. Introduce `ξ`. Apply `ENNReal.tendsto_ofReal` to reduce the goal to its premises. Apply `Tendsto.const_mul` to reduce the goal to its premises.

Apply `Tendsto.pow` to reduce the goal to its premises. Apply `Tendsto.norm` to reduce the goal to its premises. Conclude with `(tendsto_dqSymbol v ξ).smul_const _`. Establish `hfatou` using `lintegral_liminf_le' (μ := (volume : Measure E)) (u := 𝓝[≠] (0 : ℝ)) hfm`. Establish `hleft : ∫⁻ ξ, liminf (fun t ↦ f t ξ) (𝓝[≠] 0) = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) • fourierFun u ξ‖ ^ 2)`.

Use `congr 1`. Use extensionality with `ξ`. Conclude with `(hlim ξ).liminf_eq`. Establish `hright : liminf (fun t ↦ ∫⁻ ξ, f t ξ) (𝓝[≠] 0) ≤ ENNReal.ofReal (C ^ 2)`. Repeatedly rewrite using `[hnorm]`.

Apply `liminf_le_of_frequently_le'` to reduce the goal to its premises. Apply `Eventually.frequently` to reduce the goal to its premises. Use `filter_upwards [hC] with t ht`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Conclude with `pow_le_pow_left₀ (norm_nonneg _) ht 2`.

Establish `hbound` using `(hleft ▸ hfatou).trans hright`. Establish `hc2 : (0 : ℝ) < (2 * Real.pi) ^ 2` using `by positivity`. Establish `hpt : ∀ ξ : E, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ v ^ 2 * ‖fourierFun u ξ‖ ^ 2) = ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) • fourierFun u ξ‖ ^ 2)`. Introduce `ξ`. Rewrite using `[← ENNReal.ofReal_mul (by positivity)]`.

Use `congr 1`. Establish `h2pi : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi`. Rewrite using `[norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]`. Rewrite using `[norm_smul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, h2pi, Real.norm_eq_abs, mul_one, mul_pow, mul_pow, mul_pow, sq_abs]`. Clear the denominators using the available nonvanishing facts.

Repeatedly rewrite using `[hpt]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Conclude with `ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hbound.trans_lt ENNReal.ofReal_lt_top)`.
-/
theorem memSobolev_add_one_of_diffQuot {s : ℝ} (u : SobolevSpace E F s)
    (h : ∀ v : E, ∃ C, ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖SobolevSpace.diffQuot v t u‖ ≤ C) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) := by
  apply memSobolev_add_one_of_lintegral
  intro v
  obtain ⟨C, hC⟩ := h v
  set f : ℝ → E → ℝ≥0∞ := fun t ξ ↦
    ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖dqSymbol v t ξ • fourierFun u ξ‖ ^ 2)
  have hc : Continuous (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ s) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
  have hfm : ∀ t, AEMeasurable (f t) (volume : Measure E) := fun t ↦
    (hc.aestronglyMeasurable.mul (((dqSymbol_hasTemperateGrowth v t).1.continuous.aestronglyMeasurable.smul
      (fourierFun_aestronglyMeasurable u)).norm.pow 2)).aemeasurable.ennreal_ofReal
  have hnorm : ∀ t, ∫⁻ ξ, f t ξ = ENNReal.ofReal (‖SobolevSpace.diffQuot v t u‖ ^ 2) := by
    intro t
    have hm := fourierFun_multiplier (dqSymbol_hasTemperateGrowth v t)
      (bound_of_le (s := s) (norm_dqSymbol_le' v t)) u
    change _ = ENNReal.ofReal (‖SobolevSpace.multiplier _ _ u‖ ^ 2)
    rw [hm.2, ofReal_integral_eq_lintegral_ofReal]
    · have hi := integrable_weight_mul_norm_sq_fourierFun
        (SobolevSpace.multiplier (dqSymbol_hasTemperateGrowth v t)
          (bound_of_le (s := s) (norm_dqSymbol_le' v t)) u)
      refine hi.congr ?_
      filter_upwards [hm.1] with ξ hξ
      rw [hξ]
    · exact ae_of_all _ fun ξ ↦ by positivity
  have hlim : ∀ ξ, Tendsto (fun t ↦ f t ξ) (𝓝[≠] 0) (𝓝 (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s *
      ‖((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) • fourierFun u ξ‖ ^ 2))) := by
    intro ξ
    apply ENNReal.tendsto_ofReal
    apply Tendsto.const_mul
    apply Tendsto.pow
    apply Tendsto.norm
    exact (tendsto_dqSymbol v ξ).smul_const _
  have hfatou := lintegral_liminf_le' (μ := (volume : Measure E)) (u := 𝓝[≠] (0 : ℝ)) hfm
  have hleft : ∫⁻ ξ, liminf (fun t ↦ f t ξ) (𝓝[≠] 0) = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s *
      ‖((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) • fourierFun u ξ‖ ^ 2) := by
    congr 1; ext ξ; exact (hlim ξ).liminf_eq
  have hright : liminf (fun t ↦ ∫⁻ ξ, f t ξ) (𝓝[≠] 0) ≤ ENNReal.ofReal (C ^ 2) := by
    simp_rw [hnorm]
    apply liminf_le_of_frequently_le'
    apply Eventually.frequently
    filter_upwards [hC] with t ht
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hbound := (hleft ▸ hfatou).trans hright
  have hc2 : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  have hpt : ∀ ξ : E,
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ v ^ 2 * ‖fourierFun u ξ‖ ^ 2) =
        ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s *
          ‖((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) • fourierFun u ξ‖ ^ 2) := by
    intro ξ
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [norm_smul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, h2pi,
      Real.norm_eq_abs, mul_one, mul_pow, mul_pow, mul_pow, sq_abs]
    field_simp
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hbound.trans_lt ENNReal.ofReal_lt_top)

/- English proof (translation)
Apply `SobolevSpace.toDistribution_injective` to reduce the goal to its premises. Rewrite using `[SobolevSpace.toDistribution_inclusion, SobolevSpace.toDistribution_mk]`.
-/
theorem inclusion_mk_eq {s : ℝ} (u : SobolevSpace E F s)
    (hu : MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u)) :
    SobolevSpace.inclusion (le_add_of_nonneg_right zero_le_one) (SobolevSpace.mk (s := s + 1) _ hu) = u := by
  apply SobolevSpace.toDistribution_injective
  rw [SobolevSpace.toDistribution_inclusion, SobolevSpace.toDistribution_mk]

open Filter Topology in

/- English proof (translation)
Use `⟨fun hu v ↦ ⟨2 * Real.pi * ‖v‖ * ‖SobolevSpace.mk (s := s + 1) _ hu‖, Eventually.of_forall fun t ↦ ?_⟩, memSobolev_add_one_of_diffQuot u⟩` and prove the remaining obligations. Establish `h` using `SobolevSpace.norm_diffQuot_le v t (SobolevSpace.mk (s := s + 1) _ hu)`. Rewrite `h` using `[inclusion_mk_eq u hu]`. Then use the resulting hypothesis.
-/
theorem memSobolev_add_one_iff_diffQuot {s : ℝ} (u : SobolevSpace E F s) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) ↔
      ∀ v : E, ∃ C, ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖SobolevSpace.diffQuot v t u‖ ≤ C := by
  refine ⟨fun hu v ↦ ⟨2 * Real.pi * ‖v‖ * ‖SobolevSpace.mk (s := s + 1) _ hu‖,
    Eventually.of_forall fun t ↦ ?_⟩, memSobolev_add_one_of_diffQuot u⟩
  have h := SobolevSpace.norm_diffQuot_le v t (SobolevSpace.mk (s := s + 1) _ hu)
  rwa [inclusion_mk_eq u hu] at h

end

end GroundTheory.Automorphic.Sobolev
