import Mathlib
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureWideGaussianMulSchwartzStatement
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.NarrowGauss

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def gauss (c : ℝ) (hc : 0 < c) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi))
      (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv)
    (GroundTheory.Global.gaussianSchwartz E)

/- English proof (translation)
Rewrite using `[gauss, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, GroundTheory.Global.gaussianSchwartz_apply]`. Establish `h : -Real.pi * ‖(LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi)) (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv x‖ ^ 2 = -c * ‖x‖ ^ 2`. Simplify using `only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (div_pos hc Real.pi_pos).le]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h, Complex.ofReal_exp]`.

Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem gauss_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gauss c hc x = Complex.exp (-(c : ℂ) * ‖x‖ ^ 2) := by
  rw [gauss, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply]
  have h : -Real.pi * ‖(LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi))
      (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv x‖ ^ 2
      = -c * ‖x‖ ^ 2 := by
    simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (div_pos hc Real.pi_pos).le]
    field_simp
  rw [h, Complex.ofReal_exp]
  push_cast
  ring_nf

/- English proof (translation)
Rewrite using `[SchwartzMap.fourier_coe]`. Establish `: (⇑(gauss c hc) : E → ℂ) = fun v ↦ Complex.exp (-(c : ℂ) * ‖v‖ ^ 2)`. Use function extensionality and compare the values at `(gauss_apply c hc)`. Rewrite using `[this, fourier_gaussian_innerProductSpace (by simpa using hc)]`.
-/
theorem fourier_gauss (c : ℝ) (hc : 0 < c) (w : E) :
    (𝓕 (gauss (E := E) c hc) : SchwartzMap E ℂ) w = (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
      Complex.exp (-Real.pi ^ 2 * ‖w‖ ^ 2 / c) := by
  rw [SchwartzMap.fourier_coe]
  have : (⇑(gauss c hc) : E → ℂ) = fun v ↦ Complex.exp (-(c : ℂ) * ‖v‖ ^ 2) :=
    funext (gauss_apply c hc)
  rw [this, fourier_gaussian_innerProductSpace (by simpa using hc)]

/- English proof (translation)
Use `set c : ℝ := Real.pi ^ 2 / b with hc_def`. Establish `hc : 0 < c` using `by positivity`. Use `set K : ℂ := (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) with hK`. Establish `hK0 : K ≠ 0`. Rewrite using `[hK]`.

Conclude with `Complex.cpow_ne_zero_iff.2 (Or.inl (div_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast hc.ne')))`. Use `set g : SchwartzMap E ℂ := gauss c hc`. Use `set v : SchwartzMap E ℂ := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g`. Establish `huv : u = K⁻¹ • (𝓕 v : SchwartzMap E ℂ)`. Use extensionality with `ξ`.

Rewrite using `[SchwartzMap.smul_apply, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply', fourier_gauss, ← hK, hu, smul_eq_mul]`. Establish `e : Complex.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) = Complex.exp (-((b * ‖ξ‖ ^ 2 : ℝ) : ℂ))`. Use `congr 1`. Rewrite using `[hc_def]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts. Use `⟨c, K⁻¹, hc, fun y ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[huv, FourierTransform.fourierInv_smul, FourierTransform.fourierInv_fourier_eq, SchwartzMap.smul_apply, smul_eq_mul, SchwartzMap.convolution_apply, convolution_def]`.

Use `congr 1`. Use `integral_congr_ae (Eventually.of_forall fun a ↦ ?_)` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.mul_apply', g, gauss_apply]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem fourierInv_gauss_mul_eq (f u : SchwartzMap E ℂ) (b : ℝ) (hb : 0 < b)
    (hu : ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * (𝓕 f : SchwartzMap E ℂ) y) :
    ∃ (c : ℝ) (s : ℂ), 0 < c ∧ ∀ y, (𝓕⁻ u : SchwartzMap E ℂ) y =
      s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
  set c : ℝ := Real.pi ^ 2 / b with hc_def
  have hc : 0 < c := by positivity
  set K : ℂ := (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    exact Complex.cpow_ne_zero_iff.2 (Or.inl (div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (by exact_mod_cast hc.ne')))
  set g : SchwartzMap E ℂ := gauss c hc
  set v : SchwartzMap E ℂ := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g
  have huv : u = K⁻¹ • (𝓕 v : SchwartzMap E ℂ) := by
    ext ξ
    rw [SchwartzMap.smul_apply, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
      ContinuousLinearMap.mul_apply', fourier_gauss, ← hK, hu, smul_eq_mul]
    have e : Complex.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) = Complex.exp (-((b * ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
      congr 1
      rw [hc_def]
      push_cast
      field_simp
    rw [e]
    field_simp
  refine ⟨c, K⁻¹, hc, fun y ↦ ?_⟩
  rw [huv, FourierTransform.fourierInv_smul, FourierTransform.fourierInv_fourier_eq,
    SchwartzMap.smul_apply, smul_eq_mul, SchwartzMap.convolution_apply, convolution_def]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
  simp only [ContinuousLinearMap.mul_apply', g, gauss_apply]
  push_cast
  ring_nf

end GlobalTheory.NarrowGauss

open GlobalTheory.NarrowGauss in
/- English proof (translation)
Introduce `E _ _ _ _ _ f`. Establish `h1` using `GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz E (𝓕 f : SchwartzMap E ℂ)`. Establish `h2` using `map_mem_closure (f := fun w : SchwartzMap E ℂ ↦ (𝓕⁻ w : SchwartzMap E ℂ)) (t := {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧ ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))}) FourierTransform.continuous_fourierInv h1 (fun u hu ↦ by`. Take `⟨b, hb, hu⟩` from `hu`. Conclude with `fourierInv_gauss_mul_eq f u b hb hu)`.

Simplify `h2` using `[FourierTransform.fourierInv_fourier_eq]`.
-/
theorem GlobalTheory.narrowGauss_convolution_dense :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ),
    f ∈ closure {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} := by
  intro E _ _ _ _ _ f
  have h1 := GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz E (𝓕 f : SchwartzMap E ℂ)
  have h2 := map_mem_closure (f := fun w : SchwartzMap E ℂ ↦ (𝓕⁻ w : SchwartzMap E ℂ))
    (t := {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))})
    FourierTransform.continuous_fourierInv h1 (fun u hu ↦ by
      obtain ⟨b, hb, hu⟩ := hu
      exact fourierInv_gauss_mul_eq f u b hb hu)
  simpa [FourierTransform.fourierInv_fourier_eq] using h2
