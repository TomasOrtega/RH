import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAApply

noncomputable section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory.HeckeLemma

def lin (a b w : ℂ) : ℂ := a * (w.re : ℂ) + b * (w.im : ℂ)

def ker (l w : ℂ) : ℂ :=
  Complex.exp (-2 * Real.pi * ((w.re : ℂ) ^ 2 + (w.im : ℂ) ^ 2)
    - 2 * Real.pi * Complex.I * ((w.re : ℂ) * l.re + (w.im : ℂ) * l.im))

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
/- English proof (translation)
Establish `h` using `fourier_gaussian_innerProductSpace (V := ℂ) (b := 2 * (Real.pi : ℂ)) (by simp [Real.pi_pos]) l`. Establish `hf : (fun v : ℂ => Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) = fun v : ℂ => Complex.exp (-(2 * (Real.pi : ℂ)) * (‖v‖ : ℂ) ^ 2)`. Use function extensionality and compare the values at `v`. Use `push_cast`. Put the polynomial expressions in normal form.

Rewrite using `[hf, h, Complex.finrank_real_complex]`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `h1 : ((Real.pi : ℂ) / (2 * Real.pi)) ^ (((2 : ℕ) : ℂ) / 2) = 1 / 2`. Rewrite using `[show (((2 : ℕ) : ℂ) / 2) = 1 by norm_num, Complex.cpow_one]; field_simp`. Rewrite using `[h1]`.

Use `congr 2`. Rewrite using `[norm_div, Complex.norm_two]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
private theorem fourier_gaussian_two_pi (l : ℂ) :
    𝓕 (fun v : ℂ => Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ) := by
  have h := fourier_gaussian_innerProductSpace (V := ℂ) (b := 2 * (Real.pi : ℂ))
    (by simp [Real.pi_pos]) l
  have hf : (fun v : ℂ => Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) =
      fun v : ℂ => Complex.exp (-(2 * (Real.pi : ℂ)) * (‖v‖ : ℂ) ^ 2) := by
    funext v; push_cast; ring_nf
  rw [hf, h, Complex.finrank_real_complex]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : ((Real.pi : ℂ) / (2 * Real.pi)) ^ (((2 : ℕ) : ℂ) / 2) = 1 / 2 := by
    rw [show (((2 : ℕ) : ℂ) / 2) = 1 by norm_num, Complex.cpow_one]; field_simp
  rw [h1]
  congr 2
  rw [norm_div, Complex.norm_two]
  push_cast
  field_simp

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
/- English proof (translation)
Establish `h` using `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (Real.pi : ℂ)) (by simp [Real.pi_pos]) 0 0`. Use `h.norm.congr (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Simplify using `only [zero_mul, add_zero, Complex.norm_exp]`. Use `congr 1`. Simplify using `[← Complex.ofReal_pow]`.
-/
private theorem integrable_exp_neg_pi_norm_sq : Integrable (fun v : ℂ => Real.exp (-Real.pi * ‖v‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (Real.pi : ℂ))
    (by simp [Real.pi_pos]) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
/- English proof (translation)
Use `(integrable_exp_neg_pi_norm_sq.const_mul ((m.factorial : ℝ) * Real.exp 1)).mono' (by fun_prop) (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Establish `hr : 0 ≤ ‖v‖` using `norm_nonneg v`. Establish `h1 : ‖v‖ ^ m ≤ m.factorial * Real.exp ‖v‖`. Use `Real.pow_div_factorial_le_exp _ hr m` as an intermediate fact. Rewrite `this` using `[div_le_iff₀ (by positivity)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : Real.exp ‖v‖ * Real.exp (-2 * Real.pi * ‖v‖ ^ 2) ≤ Real.exp 1 * Real.exp (-Real.pi * ‖v‖ ^ 2)`. Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use polynomial arithmetic with `[Real.pi_gt_three, sq_nonneg (‖v‖ - 1 / 2)]`.

Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem integrable_pow_norm_mul_gaussian (m : ℕ) :
    Integrable (fun v : ℂ => ‖v‖ ^ m * Real.exp (-2 * Real.pi * ‖v‖ ^ 2)) := by
  refine (integrable_exp_neg_pi_norm_sq.const_mul ((m.factorial : ℝ) * Real.exp 1)).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun v => ?_)
  have hr : 0 ≤ ‖v‖ := norm_nonneg v
  have h1 : ‖v‖ ^ m ≤ m.factorial * Real.exp ‖v‖ := by
    have := Real.pow_div_factorial_le_exp _ hr m
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h2 : Real.exp ‖v‖ * Real.exp (-2 * Real.pi * ‖v‖ ^ 2) ≤
      Real.exp 1 * Real.exp (-Real.pi * ‖v‖ ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_gt_three, sq_nonneg (‖v‖ - 1 / 2)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖v‖ ^ m * Real.exp (-2 * Real.pi * ‖v‖ ^ 2)
      ≤ (m.factorial * Real.exp ‖v‖) * Real.exp (-2 * Real.pi * ‖v‖ ^ 2) := by gcongr
    _ = m.factorial * (Real.exp ‖v‖ * Real.exp (-2 * Real.pi * ‖v‖ ^ 2)) := by ring
    _ ≤ m.factorial * (Real.exp 1 * Real.exp (-Real.pi * ‖v‖ ^ 2)) := by gcongr
    _ = _ := by ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
/- English proof (translation)
Rewrite using `[norm_mul, norm_pow, Complex.norm_conj, Complex.norm_exp_ofReal]`.
-/
private theorem norm_conj_pow_mul_gaussian (n : ℕ) (v : ℂ) :
    ‖(starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)‖ =
      ‖v‖ ^ n * Real.exp (-2 * Real.pi * ‖v‖ ^ 2) := by
  rw [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_exp_ofReal]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
/- English proof (translation)
The claim follows from `(integrable_pow_norm_mul_gaussian n).mono' (by fun_prop) (Filter.Eventually.of_forall fun v => (norm_conj_pow_mul_gaussian n v).le)`.
-/
private theorem integrable_conj_pow_mul_gaussian (n : ℕ) :
    Integrable (fun v : ℂ => (starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) :=
  (integrable_pow_norm_mul_gaussian n).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun v => (norm_conj_pow_mul_gaussian n v).le)

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
/- English proof (translation)
Use `(integrable_pow_norm_mul_gaussian (n + 1)).congr (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Simplify using `only [norm_conj_pow_mul_gaussian]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem integrable_norm_mul_conj_pow_mul_gaussian (n : ℕ) :
    Integrable (fun v : ℂ =>
      ‖v‖ * ‖(starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)‖) := by
  refine (integrable_pow_norm_mul_gaussian (n + 1)).congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [norm_conj_pow_mul_gaussian]
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
/- English proof (translation)
Establish `hlin : HasFDerivAt (fun z : ℂ => z / 2) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ) l`. Use `(((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ).hasFDerivAt).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Complex.real_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hP : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) (z / 2)) ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ)) l` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp l hlin`. Establish `hN` using `(hlin.norm_sq).const_mul (-2 * Real.pi)`. Establish `hR : HasFDerivAt (fun z : ℂ => ((-2 * Real.pi * ‖z / 2‖ ^ 2 : ℝ) : ℂ)) _ l` using `Complex.ofRealCLM.hasFDerivAt.comp l hN`. Establish `hQ` using `hR.cexp`. Use `⟨_, ((hP.pow n).mul hQ).const_mul ((1 / 2 : ℂ) * (-Complex.I) ^ n), ?_⟩` and prove the remaining obligations.

Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, Complex.conjCLE_apply, Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_apply]`. Establish `c2 : (starRingEnd ℂ) 2 = 2` using `map_ofNat _ 2`. Establish `e1 : (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((1 / 2 : ℝ) • (1 : ℂ)) = 1 / 2`. Simplify using `[Complex.real_smul, c2]`. Establish `e2 : (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((1 / 2 : ℝ) • Complex.I) = -Complex.I / 2`.

Simplify using `[Complex.real_smul, c2]`. Expand and normalize the polynomial expressions, which then agree. Establish `i1 : ⟪l / 2, (1 / 2 : ℝ) • (1 : ℂ)⟫ = l.re / 4`. Simplify using `[Complex.inner, Complex.real_smul, c2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `i2 : ⟪l / 2, (1 / 2 : ℝ) • Complex.I⟫ = l.im / 4`. Simplify using `[Complex.inner, Complex.real_smul, c2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : (starRingEnd ℂ) (l / 2) = ((l.re : ℂ) - (l.im : ℂ) * Complex.I) / 2`. Apply the tactic sequence `apply Complex.ext <;> simp [c2]`.

Rewrite using `[e1, e2, i1, i2, pow_succ]`. Simplify using `only [nsmul_eq_mul]`. Use `push_cast`. Rewrite using `[hc]`. Put the polynomial expressions in normal form.

Simplify using `only [Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hasFDerivAt_conj_pow_mul_gaussian_half (n : ℕ) (l : ℂ) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun z : ℂ => (1 / 2 : ℂ) * (-Complex.I) ^ n *
        ((starRingEnd ℂ) (z / 2) ^ n * Complex.exp ((-2 * Real.pi * ‖z / 2‖ ^ 2 : ℝ) : ℂ))) L l ∧
      L 1 - Complex.I * L Complex.I = -(2 * Real.pi) * ((1 / 2 : ℂ) * (-Complex.I) ^ n *
        ((starRingEnd ℂ) (l / 2) ^ (n + 1) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ))) := by
  have hlin : HasFDerivAt (fun z : ℂ => z / 2) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ) l := by
    refine (((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ).hasFDerivAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Complex.real_smul]
    push_cast; ring
  have hP : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) (z / 2))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ)) l :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp l hlin
  have hN := (hlin.norm_sq).const_mul (-2 * Real.pi)
  have hR : HasFDerivAt (fun z : ℂ => ((-2 * Real.pi * ‖z / 2‖ ^ 2 : ℝ) : ℂ)) _ l :=
    Complex.ofRealCLM.hasFDerivAt.comp l hN
  have hQ := hR.cexp
  refine ⟨_, ((hP.pow n).mul hQ).const_mul ((1 / 2 : ℂ) * (-Complex.I) ^ n), ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, Complex.conjCLE_apply, Complex.ofRealCLM_apply, innerSL_apply_apply,
    smul_eq_mul, Function.comp_apply]
  have c2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  have e1 : (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((1 / 2 : ℝ) • (1 : ℂ)) = 1 / 2 := by
    simp [Complex.real_smul, c2]
  have e2 : (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((1 / 2 : ℝ) • Complex.I) = -Complex.I / 2 := by
    simp [Complex.real_smul, c2]; ring
  have i1 : ⟪l / 2, (1 / 2 : ℝ) • (1 : ℂ)⟫ = l.re / 4 := by
    simp [Complex.inner, Complex.real_smul, c2]; ring
  have i2 : ⟪l / 2, (1 / 2 : ℝ) • Complex.I⟫ = l.im / 4 := by
    simp [Complex.inner, Complex.real_smul, c2]; ring
  have hc : (starRingEnd ℂ) (l / 2) = ((l.re : ℂ) - (l.im : ℂ) * Complex.I) / 2 := by
    apply Complex.ext <;> simp [c2]
  rw [e1, e2, i1, i2, pow_succ]
  simp only [nsmul_eq_mul]
  push_cast
  rw [hc]
  ring_nf
  simp only [Complex.I_sq]
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
/- English proof (translation)
Establish `hS : Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) g)`. Use `(hg'.const_mul (2 * Real.pi * ‖(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)‖)).mono' hg.aestronglyMeasurable.fourierSMulRight (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hΦ` using `(Real.fourierIntegral_convergent_iff (μ := volume) l).2 hS`. Rewrite using `[Real.fourier_eq, Real.fourier_eq, ContinuousLinearMap.integral_apply hΦ, ContinuousLinearMap.integral_apply hΦ, ← integral_const_mul, ← integral_sub (hΦ.apply_continuousLinearMap 1) ((hΦ.apply_continuousLinearMap Complex.I).const_mul _), ← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `v`. Simplify using `only [ContinuousLinearMap.smul_apply, VectorFourier.fourierSMulRight_apply, Complex.inner, smul_eq_mul, Circle.smul_def]`. Establish `hc : (starRingEnd ℂ) v = (v.re : ℂ) - (v.im : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`.

Establish `h1 : ((innerSL ℝ) v : ℂ →L[ℝ] ℝ) 1 = v.re` using `by first`. Consider the case `(rw [innerSL_apply_apply]; simp [Complex.inner])`. Consider the case `(show ⟪v, (1 : ℂ)⟫ = v.re; simp [Complex.inner])`. Establish `hI : ((innerSL ℝ) v : ℂ →L[ℝ] ℝ) Complex.I = v.im` using `by first`. Consider the case `(rw [innerSL_apply_apply]; simp [Complex.inner])`.

Consider the case `(show ⟪v, Complex.I⟫ = v.im; simp [Complex.inner])`. Rewrite using `[hc, h1, hI]`. Put the polynomial expressions in normal form. Simplify using `only [Complex.I_sq, Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem fourier_fourierSMulRight_sub_I_mul_eq_fourier_conj_mul (g : ℂ → ℂ) (hg : Integrable g)
    (hg' : Integrable (fun v : ℂ => ‖v‖ * ‖g v‖)) (l : ℂ) :
    (𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) g) l) 1 -
        Complex.I * (𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) g) l) Complex.I =
      -(2 * Real.pi * Complex.I) * 𝓕 (fun v : ℂ => (starRingEnd ℂ) v * g v) l := by
  have hS : Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) g) := by
    refine (hg'.const_mul (2 * Real.pi * ‖(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)‖)).mono'
      hg.aestronglyMeasurable.fourierSMulRight (Filter.Eventually.of_forall fun v => ?_)
    calc _ ≤ 2 * Real.pi * ‖(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)‖ * ‖v‖ * ‖g v‖ :=
          VectorFourier.norm_fourierSMulRight_le _ _ _
      _ = _ := by ring
  have hΦ := (Real.fourierIntegral_convergent_iff (μ := volume) l).2 hS
  rw [Real.fourier_eq, Real.fourier_eq, ContinuousLinearMap.integral_apply hΦ,
    ContinuousLinearMap.integral_apply hΦ, ← integral_const_mul,
    ← integral_sub (hΦ.apply_continuousLinearMap 1) ((hΦ.apply_continuousLinearMap Complex.I).const_mul _),
    ← integral_const_mul]
  congr 1
  funext v
  simp only [ContinuousLinearMap.smul_apply, VectorFourier.fourierSMulRight_apply,
    Complex.inner, smul_eq_mul, Circle.smul_def]
  have hc : (starRingEnd ℂ) v = (v.re : ℂ) - (v.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have h1 : ((innerSL ℝ) v : ℂ →L[ℝ] ℝ) 1 = v.re := by
    first
    | (rw [innerSL_apply_apply]; simp [Complex.inner])
    | (show ⟪v, (1 : ℂ)⟫ = v.re; simp [Complex.inner])
  have hI : ((innerSL ℝ) v : ℂ →L[ℝ] ℝ) Complex.I = v.im := by
    first
    | (rw [innerSL_apply_apply]; simp [Complex.inner])
    | (show ⟪v, Complex.I⟫ = v.im; simp [Complex.inner])
  rw [hc, h1, hI]
  ring_nf
  simp only [Complex.I_sq, Complex.real_smul]
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro l`. Simplify using `using fourier_gaussian_two_pi l`. Consider the case `succ n ih`. Introduce `l`.

Establish `hF : 𝓕 (fun v : ℂ => (starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) = fun z : ℂ => (1 / 2 : ℂ) * (-Complex.I) ^ n * ((starRingEnd ℂ) (z / 2) ^ n * Complex.exp ((-2 * Real.pi * ‖z / 2‖ ^ 2 : ℝ) : ℂ))`. Use function extensionality and compare the values at `ih`. Establish `hd` using `Real.hasFDerivAt_fourier (integrable_conj_pow_mul_gaussian n) (integrable_norm_mul_conj_pow_mul_gaussian n) l`. Rewrite `hd` using `[hF]`. Take `⟨L, hL, hLv⟩` from `hasFDerivAt_conj_pow_mul_gaussian_half n l`.

Establish `heq` using `hd.unique hL`. Establish `hA` using `fourier_fourierSMulRight_sub_I_mul_eq_fourier_conj_mul _ (integrable_conj_pow_mul_gaussian n) (integrable_norm_mul_conj_pow_mul_gaussian n) l`. Rewrite `hA` using `[heq, hLv]`. Establish `hfun : (fun v : ℂ => (starRingEnd ℂ) v * ((starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ))) = fun v : ℂ => (starRingEnd ℂ) v ^ (n + 1) * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)`. Use function extensionality and compare the values at `v`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hA` using `[hfun]`. Establish `h2pi : -(2 * (Real.pi : ℂ) * Complex.I) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Apply `mul_left_cancel₀ h2pi` to reduce the goal to its premises.

Rewrite using `[← hA]`. Take the linear combination `(-(2 * (Real.pi : ℂ)) * ((1 / 2 : ℂ) * (-Complex.I) ^ n * ((starRingEnd ℂ) (l / 2) ^ (n + 1) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)))) * Complex.I_sq`.
-/
private theorem fourier_conj_pow_mul_gaussian (n : ℕ) : ∀ l : ℂ,
    𝓕 (fun v : ℂ => (starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * (-Complex.I) ^ n *
        ((starRingEnd ℂ) (l / 2) ^ n * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  induction n with
  | zero => intro l; simpa using fourier_gaussian_two_pi l
  | succ n ih =>
    intro l
    have hF : 𝓕 (fun v : ℂ => (starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) =
        fun z : ℂ => (1 / 2 : ℂ) * (-Complex.I) ^ n *
          ((starRingEnd ℂ) (z / 2) ^ n * Complex.exp ((-2 * Real.pi * ‖z / 2‖ ^ 2 : ℝ) : ℂ)) :=
      funext ih
    have hd := Real.hasFDerivAt_fourier (integrable_conj_pow_mul_gaussian n)
      (integrable_norm_mul_conj_pow_mul_gaussian n) l
    rw [hF] at hd
    obtain ⟨L, hL, hLv⟩ := hasFDerivAt_conj_pow_mul_gaussian_half n l
    have heq := hd.unique hL
    have hA := fourier_fourierSMulRight_sub_I_mul_eq_fourier_conj_mul _ (integrable_conj_pow_mul_gaussian n)
      (integrable_norm_mul_conj_pow_mul_gaussian n) l
    rw [heq, hLv] at hA
    have hfun : (fun v : ℂ => (starRingEnd ℂ) v *
        ((starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ))) =
        fun v : ℂ => (starRingEnd ℂ) v ^ (n + 1) * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ) := by
      funext v; ring
    rw [hfun] at hA
    have h2pi : -(2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ h2pi
    rw [← hA]
    linear_combination (-(2 * (Real.pi : ℂ)) * ((1 / 2 : ℂ) * (-Complex.I) ^ n *
      ((starRingEnd ℂ) (l / 2) ^ (n + 1) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)))) *
      Complex.I_sq

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
/- English proof (translation)
Establish `hconj : 𝓕 (fun v : ℂ => v ^ m * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l = (starRingEnd ℂ) (𝓕 (fun v : ℂ => (starRingEnd ℂ) v ^ m * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) (-l))`. Rewrite using `[Real.fourier_eq, Real.fourier_eq, ← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Simplify using `only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, map_mul, map_pow, Complex.conj_conj, ← Complex.exp_conj, Complex.conj_ofReal, inner_neg_right, Complex.conj_I]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hconj, fourier_conj_pow_mul_gaussian m (-l)]`. Simplify using `only [map_mul, map_pow, map_neg, Complex.conj_conj, Complex.conj_I, ← Complex.exp_conj, Complex.conj_ofReal, neg_div, norm_neg, map_div₀, map_one, map_ofNat]`.

Rewrite using `[neg_pow (l / 2), neg_pow Complex.I]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem fourier_pow_mul_gaussian (m : ℕ) (l : ℂ) :
    𝓕 (fun v : ℂ => v ^ m * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * (-Complex.I) ^ m *
        ((l / 2) ^ m * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  have hconj : 𝓕 (fun v : ℂ => v ^ m * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l =
      (starRingEnd ℂ) (𝓕 (fun v : ℂ => (starRingEnd ℂ) v ^ m *
        Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) (-l)) := by
    rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
    congr 1
    funext v
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, map_mul, map_pow,
      Complex.conj_conj, ← Complex.exp_conj, Complex.conj_ofReal, inner_neg_right, Complex.conj_I]
    congr 2
    push_cast
    ring
  rw [hconj, fourier_conj_pow_mul_gaussian m (-l)]
  simp only [map_mul, map_pow, map_neg, Complex.conj_conj, Complex.conj_I, ← Complex.exp_conj,
    Complex.conj_ofReal, neg_div, norm_neg, map_div₀, map_one, map_ofNat]
  rw [neg_pow (l / 2), neg_pow Complex.I]
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in

/- English proof (translation)
Introduce `k l`. Unfold `_root_.GlobalTheory.HeckeTheta.hmon`. Distinguish the cases in `hk : 0 ≤ k`. Simplify using `only [hk, ↓reduceIte]`. Rewrite using `[show k.natAbs = k.toNat by omega]`.

Conclude with `fourier_conj_pow_mul_gaussian k.toNat l`. Simplify using `only [hk, ↓reduceIte]`. Rewrite using `[show k.natAbs = (-k).toNat by omega]`. Conclude with `fourier_pow_mul_gaussian (-k).toNat l`.
-/
theorem _root_.GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian : ∀ (k : ℤ) (l : ℂ),
    𝓕 (fun w : ℂ => _root_.GlobalTheory.HeckeTheta.hmon k w *
        Complex.exp ((-2 * Real.pi * ‖w‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * (-Complex.I) ^ k.natAbs * (_root_.GlobalTheory.HeckeTheta.hmon k (l / 2) *
        Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  intro k l
  unfold _root_.GlobalTheory.HeckeTheta.hmon
  by_cases hk : 0 ≤ k
  · simp only [hk, ↓reduceIte]
    rw [show k.natAbs = k.toNat by omega]
    exact fourier_conj_pow_mul_gaussian k.toNat l
  · simp only [hk, ↓reduceIte]
    rw [show k.natAbs = (-k).toNat by omega]
    exact fourier_pow_mul_gaussian (-k).toNat l

end GlobalTheory.HeckeLemma
