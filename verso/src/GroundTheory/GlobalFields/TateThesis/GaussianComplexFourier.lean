import Mathlib
import GroundTheory.GlobalFields.TateThesis.GaussianComplex

namespace GroundTheory.Global

open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform

noncomputable section

/- English proof (translation)
Establish `h` using `VectorFourier.hasFDerivAt_fourierIntegral traceFormℂ hf hf' w`. Rewrite `h` using `[← complexFourier_eq_fourierIntegral]`. Rewrite using `[hD.unique h]`. Establish `hint : Integrable (fun z ↦ VectorFourier.fourierSMulRight traceFormℂ f z) complexPlaceMeasure`. Use `((hf'.const_mul (2 * π * ‖traceFormℂ‖))).mono' hf.1.fourierSMulRight ?_` and prove the remaining obligations.

Use `Filter.Eventually.of_forall fun z ↦ ?_` and prove the remaining obligations. Use `VectorFourier.norm_fourierSMulRight_le traceFormℂ f z` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Rewrite using `[fourierIntegral_continuousLinearMap_apply' hint, fourierIntegral_continuousLinearMap_apply' hint]`. Establish `hL : ∀ v : ℂ, traceFormℂ.toLinearMap₁₂ v w = 2 * (v * w).re` using `fun v ↦ traceFormℂ_apply v w`.

Simplify using `only [VectorFourier.fourierIntegral, VectorFourier.fourierSMulRight_apply, hL, traceFormℂ_apply]`. Establish `i1 : ∀ h : ℂ, Integrable (fun z ↦ 𝐞 (-(2 * (z * w).re)) • (-(2 * π * I) • (2 * (z * h).re) • f z)) complexPlaceMeasure`. Introduce `h`. Establish `: Integrable (fun z ↦ (-(2 * π * I) • (2 * (z * h).re) • f z)) complexPlaceMeasure`. Use `(hint.apply_continuousLinearMap h)` as an intermediate fact.

Simplify `this` using `[VectorFourier.fourierSMulRight_apply]`. Use `(fourierIntegral_convergent_iff' (μ := complexPlaceMeasure) traceFormℂ w).2 this` as an intermediate fact. Simplify using `using this`. Rewrite using `[← integral_const_mul, ← integral_sub (i1 1) ((i1 I).const_mul I), complexFourier, ← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `z`. Simplify using `only [Circle.smul_def, smul_eq_mul, Complex.real_smul, mul_one, mul_I_re]`. Use `push_cast`. Establish `hz : (z : ℂ) = z.re + z.im * I` using `(re_add_im z).symm`. Take the linear combination `(-4 * π * I * (𝐞 (-(2 * (z * w).re)) : ℂ) * f z) * hz`.
-/
theorem complexFourier_mul_self {f : ℂ → ℂ} (hf : Integrable f complexPlaceMeasure)
    (hf' : Integrable (fun z ↦ ‖z‖ * ‖f z‖) complexPlaceMeasure) {w : ℂ} {D : ℂ →L[ℝ] ℂ}
    (hD : HasFDerivAt (complexFourier f) D w) :
    -4 * π * I * complexFourier (fun z ↦ z * f z) w = D 1 - I * D I := by
  have h := VectorFourier.hasFDerivAt_fourierIntegral traceFormℂ hf hf' w
  rw [← complexFourier_eq_fourierIntegral] at h
  rw [hD.unique h]
  have hint : Integrable (fun z ↦ VectorFourier.fourierSMulRight traceFormℂ f z)
      complexPlaceMeasure := by
    refine ((hf'.const_mul (2 * π * ‖traceFormℂ‖))).mono' hf.1.fourierSMulRight ?_
    refine Filter.Eventually.of_forall fun z ↦ ?_
    have := VectorFourier.norm_fourierSMulRight_le traceFormℂ f z
    simpa [mul_assoc] using this
  rw [fourierIntegral_continuousLinearMap_apply' hint,
    fourierIntegral_continuousLinearMap_apply' hint]
  have hL : ∀ v : ℂ, traceFormℂ.toLinearMap₁₂ v w = 2 * (v * w).re :=
    fun v ↦ traceFormℂ_apply v w
  simp only [VectorFourier.fourierIntegral, VectorFourier.fourierSMulRight_apply, hL,
    traceFormℂ_apply]
  have i1 : ∀ h : ℂ, Integrable (fun z ↦ 𝐞 (-(2 * (z * w).re)) •
      (-(2 * π * I) • (2 * (z * h).re) • f z)) complexPlaceMeasure := by
    intro h
    have : Integrable (fun z ↦ (-(2 * π * I) • (2 * (z * h).re) • f z)) complexPlaceMeasure := by
      have := (hint.apply_continuousLinearMap h)
      simpa [VectorFourier.fourierSMulRight_apply] using this
    have := (fourierIntegral_convergent_iff' (μ := complexPlaceMeasure) traceFormℂ w).2 this
    simpa using this
  rw [← integral_const_mul, ← integral_sub (i1 1) ((i1 I).const_mul I), complexFourier,
    ← integral_const_mul]
  congr 1
  funext z
  simp only [Circle.smul_def, smul_eq_mul, Complex.real_smul, mul_one, mul_I_re]
  push_cast
  have hz : (z : ℂ) = z.re + z.im * I := (re_add_im z).symm
  linear_combination (-4 * π * I * (𝐞 (-(2 * (z * w).re)) : ℂ) * f z) * hz

/- English proof (translation)
Use `congr 2`. Rewrite using `[mul_conj, normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cexp_neg_two_pi_norm_sq (w : ℂ) :
    Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2) = Complex.exp (-2 * π * (w * conj w)) := by
  congr 2
  rw [mul_conj, normSq_eq_norm_sq]
  push_cast
  ring

/- English proof (translation)
Simplify using `only [cexp_neg_two_pi_norm_sq]`. Establish `hc : HasFDerivAt (fun w : ℂ ↦ conj w) (conjCLE : ℂ →L[ℝ] ℂ) w` using `(conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt`. Establish `hid : HasFDerivAt (fun w : ℂ ↦ w) (ContinuousLinearMap.id ℝ ℂ) w` using `hasFDerivAt_id w`. Establish `hq` using `(hid.fun_mul hc).const_mul (-2 * π : ℂ)`. Establish `hexp` using `hq.cexp`.

Establish `hp` using `hc.pow n`. Use `⟨_, hp.fun_mul hexp, ?_⟩` and prove the remaining obligations. Simplify using `only [add_apply, smul_apply, ContinuousLinearMap.coe_id', id, ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_one, conj_I, smul_eq_mul, nsmul_eq_mul]`. Rewrite using `[pow_succ]`. Take the linear combination `(conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * (-2 * π) * (-w) + Complex.exp (-2 * π * (w * conj w)) * (n * conj w ^ (n - 1)) + 2 * conj w * conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * π - 4 * conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * π * w) * I_sq`.
-/
theorem exists_hasFDerivAt_conj_pow_mul_gaussian (n : ℕ) (w : ℂ) :
    ∃ D : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun w : ℂ ↦ conj w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) D w ∧
      D 1 - I * D I = -4 * π * (conj w ^ (n + 1) * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by
  simp only [cexp_neg_two_pi_norm_sq]
  have hc : HasFDerivAt (fun w : ℂ ↦ conj w) (conjCLE : ℂ →L[ℝ] ℂ) w :=
    (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
  have hid : HasFDerivAt (fun w : ℂ ↦ w) (ContinuousLinearMap.id ℝ ℂ) w := hasFDerivAt_id w
  have hq := (hid.fun_mul hc).const_mul (-2 * π : ℂ)
  have hexp := hq.cexp
  have hp := hc.pow n
  refine ⟨_, hp.fun_mul hexp, ?_⟩
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_id', id, ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_one,
    conj_I, smul_eq_mul, nsmul_eq_mul]
  rw [pow_succ]
  linear_combination (conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * (-2 * π) * (-w) +
    Complex.exp (-2 * π * (w * conj w)) * (n * conj w ^ (n - 1)) +
    2 * conj w * conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * π -
    4 * conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * π * w) * I_sq

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `[complexGaussian]`.
-/
theorem complexGaussian_natCast (n : ℕ) :
    complexGaussian n = fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  funext z
  simp [complexGaussian]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Rewrite using `[complexGaussian]`. Use `split_ifs with h`. Establish `: n = 0` using `by omega`. Substitute `this` using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem complexGaussian_neg_natCast (n : ℕ) :
    complexGaussian (-(n : ℤ)) = fun z ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  funext z
  rw [complexGaussian]
  split_ifs with h
  · have : n = 0 := by omega
    subst this; simp
  · simp

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `complexFourier_complexGaussian_zero`. Simplify using `only [funext complexGaussian_zero] at h`. Simplify using `using h`.

Consider the case `succ n ih`. Use function extensionality and compare the values at `w`. Take `⟨D, hD, hD1⟩` from `exists_hasFDerivAt_conj_pow_mul_gaussian n w`. Establish `hF : HasFDerivAt (complexFourier (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2))) ((-I) ^ n • D) w`. Rewrite using `[ih]`.

Conclude with `hD.const_mul _`. Establish `hf : Integrable (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) complexPlaceMeasure`. Simplify `integrable_complexGaussian n` using `[complexGaussian_natCast]`. Establish `hf' : Integrable (fun z ↦ ‖z‖ * ‖z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)‖) complexPlaceMeasure`. Use `(integrable_norm_pow_smul_complexGaussian' n 1).norm` as an intermediate fact.

Use `this.congr (Filter.Eventually.of_forall fun z ↦ ?_)` and prove the remaining obligations. Simplify using `[complexGaussian_natCast]`. Establish `key` using `complexFourier_mul_self hf hf' hF`. Establish `e : (fun z : ℂ ↦ z * (z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2))) = fun z ↦ z ^ (n + 1) * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)`. Use function extensionality and compare the values at `z`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[e]`. Establish `hne : (-4 * π * I : ℂ) ≠ 0`. Establish `: (π : ℂ) ≠ 0` using `ofReal_ne_zero.mpr Real.pi_ne_zero`. Simplify using `[this, I_ne_zero]`.

Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[key]`. Simplify using `only [smul_apply, smul_eq_mul]`. Establish `hD1' : (-I) ^ n * D 1 - I * ((-I) ^ n * D I) = (-I) ^ n * (D 1 - I * D I)` using `by ring`. Rewrite using `[hD1', hD1]`.

Rewrite using `[pow_succ]`. Take the linear combination `(-4 * π * (-I) ^ n * (conj w ^ (n + 1) * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2))) * I_sq`.
-/
theorem complexFourier_pow_mul_gaussian (n : ℕ) :
    complexFourier (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun w ↦ (-I) ^ n * (conj w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by
  induction n with
  | zero =>
    have h := complexFourier_complexGaussian_zero
    simp only [funext complexGaussian_zero] at h
    simpa using h
  | succ n ih =>
    funext w
    obtain ⟨D, hD, hD1⟩ := exists_hasFDerivAt_conj_pow_mul_gaussian n w
    have hF : HasFDerivAt (complexFourier (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)))
        ((-I) ^ n • D) w := by
      rw [ih]; exact hD.const_mul _
    have hf : Integrable (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2))
        complexPlaceMeasure := by
      simpa [complexGaussian_natCast] using integrable_complexGaussian n
    have hf' : Integrable (fun z ↦ ‖z‖ * ‖z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)‖)
        complexPlaceMeasure := by
      have := (integrable_norm_pow_smul_complexGaussian' n 1).norm
      refine this.congr (Filter.Eventually.of_forall fun z ↦ ?_)
      simp [complexGaussian_natCast]
    have key := complexFourier_mul_self hf hf' hF
    have e : (fun z : ℂ ↦ z * (z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2))) =
        fun z ↦ z ^ (n + 1) * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
      funext z; ring
    rw [e] at key
    have hne : (-4 * π * I : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      simp [this, I_ne_zero]
    apply mul_left_cancel₀ hne
    rw [key]
    simp only [smul_apply, smul_eq_mul]
    have hD1' : (-I) ^ n * D 1 - I * ((-I) ^ n * D I) = (-I) ^ n * (D 1 - I * D I) := by ring
    rw [hD1', hD1]
    rw [pow_succ]
    linear_combination (-4 * π * (-I) ^ n * (conj w ^ (n + 1) *
      Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2))) * I_sq

/- English proof (translation)
Rewrite using `[complexFourier, complexFourier, ← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Simplify using `only [Circle.smul_def, smul_eq_mul, map_mul, Real.fourierChar_apply, ← exp_conj]`. Use `congr 2`.

Simplify using `only [conj_ofReal, conj_I]`. Use `push_cast`. Simplify using `only [neg_mul, mul_neg, neg_re, mul_re, ofReal_neg, ofReal_sub, ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem complexFourier_conj (f : ℂ → ℂ) (w : ℂ) :
    complexFourier (fun z ↦ conj (f z)) w = conj (complexFourier f (-w)) := by
  rw [complexFourier, complexFourier, ← integral_conj]
  congr 1
  funext z
  simp only [Circle.smul_def, smul_eq_mul, map_mul, Real.fourierChar_apply, ← exp_conj]
  congr 2
  simp only [conj_ofReal, conj_I]
  push_cast
  simp only [neg_mul, mul_neg, neg_re, mul_re, ofReal_neg, ofReal_sub, ofReal_mul]
  ring

/- English proof (translation)
Rewrite using `[← exp_conj]`. Simplify using `[map_mul, conj_ofReal, map_ofNat]`.
-/
theorem conj_cexp_neg_two_pi_norm_sq (z : ℂ) :
    conj (Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) = Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  rw [← exp_conj]
  simp [map_mul, conj_ofReal, map_ofNat]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Establish `e : (fun z : ℂ ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) = fun z ↦ conj (z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2))`. Use function extensionality and compare the values at `z`. Rewrite using `[map_mul, map_pow, conj_cexp_neg_two_pi_norm_sq]`. Rewrite using `[e, complexFourier_conj, complexFourier_pow_mul_gaussian]`.

Simplify using `only [map_mul, map_pow, map_neg, conj_I, conj_conj, conj_cexp_neg_two_pi_norm_sq, norm_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem complexFourier_conj_pow_mul_gaussian (n : ℕ) :
    complexFourier (fun z ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun w ↦ (-I) ^ n * (w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by
  funext w
  have e : (fun z : ℂ ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun z ↦ conj (z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) := by
    funext z
    rw [map_mul, map_pow, conj_cexp_neg_two_pi_norm_sq]
  rw [e, complexFourier_conj, complexFourier_pow_mul_gaussian]
  simp only [map_mul, map_pow, map_neg, conj_I, conj_conj, conj_cexp_neg_two_pi_norm_sq,
    norm_neg]
  ring

/- English proof (translation)
Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg m`. Rewrite using `[complexGaussian_natCast, complexFourier_pow_mul_gaussian, complexGaussian_neg_natCast]`. Simplify using the standard rewrite rules. Rewrite using `[complexGaussian_neg_natCast, complexFourier_conj_pow_mul_gaussian, neg_neg, complexGaussian_natCast]`. Simplify using the standard rewrite rules.
-/
theorem complexFourier_complexGaussian (m : ℤ) :
    complexFourier (complexGaussian m) = fun w ↦ (-I) ^ m.natAbs * complexGaussian (-m) w := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [complexGaussian_natCast, complexFourier_pow_mul_gaussian, complexGaussian_neg_natCast]
    simp
  · rw [complexGaussian_neg_natCast, complexFourier_conj_pow_mul_gaussian, neg_neg,
      complexGaussian_natCast]
    simp

end

end GroundTheory.Global
