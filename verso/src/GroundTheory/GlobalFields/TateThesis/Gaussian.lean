import Mathlib

namespace GroundTheory.Global

open Complex MeasureTheory Set Real
open scoped FourierTransform

noncomputable section

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Put the polynomial expressions in normal form.

Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mellin_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {a : ℂ} (ha : 0 < a.re) :
    mellin (fun t : ℝ ↦ ((Real.exp (-(b * t ^ 2)) : ℝ) : ℂ)) a =
      (1 / 2 : ℂ) * (b : ℂ) ^ (-(a / 2)) * Complex.Gamma (a / 2) := by
  have h1 := mellin_comp_rpow (fun u : ℝ ↦ ((Real.exp (-(b * u)) : ℝ) : ℂ)) a 2
  simp only [Real.rpow_two] at h1
  rw [h1, mellin_comp_mul_left (fun u : ℝ ↦ ((Real.exp (-u) : ℝ) : ℂ)) _ hb,
    ← GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral (by simpa using div_pos ha two_pos)]
  simp only [abs_two, ofReal_ofNat, smul_eq_mul]
  ring_nf
  norm_num
  ring

def realGaussian (x : ℝ) : ℂ := Complex.exp (-π * (x : ℂ) ^ 2)

def realGaussianOdd (x : ℝ) : ℂ := (x : ℂ) * Complex.exp (-π * (x : ℂ) ^ 2)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem realGaussian_eq_ofReal (x : ℝ) :
    realGaussian x = ((Real.exp (-(π * x ^ 2)) : ℝ) : ℂ) := by
  simp [realGaussian, ofReal_exp]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem fourier_realGaussian : 𝓕 realGaussian = realGaussian := by
  have h := fourier_gaussian_pi (b := 1) (by simp)
  simp only [mul_one, one_cpow, div_one, one_mul] at h
  unfold realGaussian
  rw [h]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem integrable_realGaussian : Integrable realGaussian := by
  exact integrable_cexp_neg_mul_sq (b := (π : ℂ)) (by simpa using Real.pi_pos)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem integrable_realGaussianOdd : Integrable realGaussianOdd := by
  exact integrable_mul_cexp_neg_mul_sq (b := (π : ℂ)) (by simpa using Real.pi_pos)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Replace the relevant objects with their definitions. Apply an available result and prove the equalities needed to match it to the conclusion.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_realGaussian (x : ℝ) :
    HasDerivAt realGaussian (-2 * π * x * realGaussian x) x := by
  have h : HasDerivAt (fun y : ℝ ↦ -π * (y : ℂ) ^ 2) (-π * (2 * (x : ℂ))) x := by
    have := ((hasDerivAt_id x).ofReal_comp).pow 2
    simpa using this.const_mul (-(π : ℂ))
  unfold realGaussian
  convert h.cexp using 1
  ring

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

Put the polynomial expressions in normal form. Simplify using the standard rewrite rules.
-/
theorem fourier_realGaussianOdd : 𝓕 realGaussianOdd = fun y ↦ -I * realGaussianOdd y := by
  have hxf : Integrable (fun x : ℝ ↦ x • realGaussian x) := by
    refine integrable_realGaussianOdd.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [realGaussianOdd, realGaussian, Complex.real_smul]
  funext y
  have hd := hasDerivAt_fourier integrable_realGaussian hxf y
  rw [fourier_realGaussian] at hd
  have h2 := (hasDerivAt_realGaussian y).unique hd
  have h3 : 𝓕 (fun x : ℝ ↦ (-2 * π * I * x) • realGaussian x) y =
      (-2 * π * I) * 𝓕 realGaussianOdd y := by
    rw [fourier_real_eq, fourier_real_eq, ← integral_const_mul]
    congr 1; funext x
    simp only [realGaussianOdd, realGaussian, Circle.smul_def, smul_eq_mul]
    ring
  rw [h3] at h2
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have : 𝓕 realGaussianOdd y = (-2 * π * y * realGaussian y) / (-2 * π * I) := by
    rw [h2]; field_simp
  rw [this, realGaussianOdd, realGaussian]
  field_simp
  ring_nf
  simp [I_sq]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem integral_comp_abs_complex (f : ℝ → ℂ) :
    ∫ x : ℝ, f |x| = 2 * ∫ y in Ioi (0 : ℝ), f y := by
  have h := integral_fun_norm_addHaar (volume : Measure ℝ) f
  simp only [Real.norm_eq_abs] at h
  rw [h]
  simp [Complex.real_smul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Put the polynomial expressions in normal form.
-/
theorem mellin_exp_neg_pi_mul_sq {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ ↦ ((Real.exp (-(π * t ^ 2)) : ℝ) : ℂ)) s = Gammaℝ s / 2 := by
  rw [mellin_exp_neg_mul_sq Real.pi_pos hs, Gammaℝ_def]
  ring_nf

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem ofReal_cpow_div_self {y : ℝ} (hy : 0 < y) (s : ℂ) :
    (y : ℂ) ^ s / (y : ℂ) = (y : ℂ) ^ (s - 1) := by
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  rw [cpow_sub _ _ hy', cpow_one]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_realGaussian_mul_abs_cpow {s : ℂ} (hs : 0 < s.re) :
    ∫ x : ℝ, realGaussian x * ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ) = Gammaℝ s := by
  have h : (fun x : ℝ ↦ realGaussian x * ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ)) =
      fun x ↦ (fun y : ℝ ↦ ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ)) |x| := by
    funext x
    simp only [realGaussian_eq_ofReal, sq_abs]
  rw [h, integral_comp_abs_complex
    (fun y : ℝ ↦ ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ))]
  have : ∫ y in Ioi (0 : ℝ), ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ) =
      mellin (fun t : ℝ ↦ ((Real.exp (-(π * t ^ 2)) : ℝ) : ℂ)) s := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    rw [mul_div_assoc, ofReal_cpow_div_self hy, smul_eq_mul, mul_comm]
  rw [this, mellin_exp_neg_pi_mul_sq hs]
  ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_realGaussianOdd_mul_sign_mul_abs_cpow {s : ℂ} (hs : -1 < s.re) :
    ∫ x : ℝ, realGaussianOdd x * (Real.sign x : ℂ) * ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ) =
      Gammaℝ (s + 1) := by
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have h : (fun x : ℝ ↦ realGaussianOdd x * (Real.sign x : ℂ) * ((|x| : ℝ) : ℂ) ^ s /
        ((|x| : ℝ) : ℂ)) =
      fun x ↦ (fun y : ℝ ↦ (y : ℂ) * ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s /
        (y : ℂ)) |x| := by
    funext x
    have hx : (x : ℂ) * (Real.sign x : ℂ) = ((|x| : ℝ) : ℂ) := by
      rw [← ofReal_mul]
      congr 1
      rcases lt_trichotomy x 0 with h | h | h
      · rw [Real.sign_of_neg h, abs_of_neg h]; ring
      · simp [h]
      · rw [Real.sign_of_pos h, abs_of_pos h]; ring
    rw [realGaussianOdd, ← realGaussian, realGaussian_eq_ofReal]
    simp only [sq_abs]
    rw [← hx]
    ring
  rw [h, integral_comp_abs_complex
    (fun y : ℝ ↦ (y : ℂ) * ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ))]
  have : ∫ y in Ioi (0 : ℝ), (y : ℂ) * ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ)
      = mellin (fun t : ℝ ↦ ((Real.exp (-(π * t ^ 2)) : ℝ) : ℂ)) (s + 1) := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
    rw [add_sub_cancel_right, smul_eq_mul]
    field_simp
  rw [this, mellin_exp_neg_pi_mul_sq hs1]
  ring

end

end GroundTheory.Global
