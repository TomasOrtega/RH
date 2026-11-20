import Mathlib
open MeasureTheory

private noncomputable def gE (y s : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * (s * starRingEnd ℂ s) -
    (Real.pi : ℂ) * Complex.I * (s * y + starRingEnd ℂ s * starRingEnd ℂ y))

/- English proof (translation)
Rewrite using `[gE, ← Complex.exp_add, Complex.mul_conj', Complex.re_eq_add_conj, map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma gE_eq (y s : ℂ) : gE y s = Complex.exp (-(Real.pi : ℂ) * (‖s‖ : ℂ) ^ 2) *
    Complex.exp (-(2 * Real.pi * Complex.I) * (((s * y).re : ℝ) : ℂ)) := by
  rw [gE, ← Complex.exp_add, Complex.mul_conj', Complex.re_eq_add_conj, map_mul]
  congr 1
  ring

/- English proof (translation)
Rewrite using `[gE_eq, norm_mul, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]`. Use `congr 1`. Simplify using `[← Complex.ofReal_pow]`.
-/
private lemma gE_norm (y s : ℂ) : ‖gE y s‖ = Real.exp (-Real.pi * ‖s‖ ^ 2) := by
  rw [gE_eq, norm_mul, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [← Complex.ofReal_pow]

/- English proof (translation)
Unfold `gE`. Use `Complex.continuous_conj` as an intermediate fact. Use `fun_prop`.
-/
private lemma gE_cont (y : ℂ) : Continuous (gE y) := by
  unfold gE
  have := Complex.continuous_conj
  fun_prop

/- English proof (translation)
Establish `hb : 0 < (((Real.pi - 1 : ℝ)) : ℂ).re`. Rewrite using `[Complex.ofReal_re]`. Combine the linear relations using `[Real.pi_gt_three]`. Establish `h` using `(GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0).norm`. Use `Integrable.mono' (h.const_mul (((a + b).factorial : ℝ) * Real.exp 1)) ?_ ?_` and prove the remaining obligations.

Use `Complex.continuous_conj` as an intermediate fact. Use `gE_cont y` as an intermediate fact. Apply `Continuous.aestronglyMeasurable` to reduce the goal to its premises. Use `fun_prop`. Use `Filter.Eventually.of_forall fun s => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, gE_norm, Complex.norm_exp, ← pow_add]`. Establish `e : (-((Real.pi - 1 : ℝ) : ℂ) * (‖s‖ : ℂ) ^ 2 + 0 * ((inner ℝ (0 : ℂ) s : ℝ) : ℂ)).re = -(Real.pi - 1) * ‖s‖ ^ 2`. Simplify using `[← Complex.ofReal_pow]`. Rewrite using `[e]`. Establish `h1` using `Real.pow_div_factorial_le_exp ‖s‖ (norm_nonneg s) (a + b)`.

Establish `hf : (0 : ℝ) < ((a + b).factorial : ℝ)` using `by positivity`. Rewrite `h1` using `[div_le_iff₀ hf]`. Establish `h2 : Real.exp ‖s‖ ≤ Real.exp (1 + ‖s‖ ^ 2)`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use polynomial arithmetic with `[sq_nonneg (‖s‖ - 1)]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `h1.trans (by gcongr)`. Use `_ = _ := by`. Rewrite using `[show -(Real.pi - 1) * ‖s‖ ^ 2 = ‖s‖ ^ 2 + -Real.pi * ‖s‖ ^ 2 by ring, Real.exp_add, Real.exp_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma gE_int (y : ℂ) (a b : ℕ) :
    Integrable (fun s : ℂ => s ^ a * (starRingEnd ℂ s) ^ b * gE y s) := by
  have hb : 0 < (((Real.pi - 1 : ℝ)) : ℂ).re := by
    rw [Complex.ofReal_re]; linarith [Real.pi_gt_three]
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0).norm
  refine Integrable.mono' (h.const_mul (((a + b).factorial : ℝ) * Real.exp 1)) ?_ ?_
  · have := Complex.continuous_conj
    have := gE_cont y
    apply Continuous.aestronglyMeasurable
    fun_prop
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, gE_norm, Complex.norm_exp,
      ← pow_add]
    have e : (-((Real.pi - 1 : ℝ) : ℂ) * (‖s‖ : ℂ) ^ 2 + 0 * ((inner ℝ (0 : ℂ) s : ℝ) : ℂ)).re
        = -(Real.pi - 1) * ‖s‖ ^ 2 := by
      simp [← Complex.ofReal_pow]
    rw [e]
    have h1 := Real.pow_div_factorial_le_exp ‖s‖ (norm_nonneg s) (a + b)
    have hf : (0 : ℝ) < ((a + b).factorial : ℝ) := by positivity
    rw [div_le_iff₀ hf] at h1
    have h2 : Real.exp ‖s‖ ≤ Real.exp (1 + ‖s‖ ^ 2) := by
      apply Real.exp_le_exp.2
      nlinarith [sq_nonneg (‖s‖ - 1)]
    calc ‖s‖ ^ (a + b) * Real.exp (-Real.pi * ‖s‖ ^ 2)
        ≤ (Real.exp (1 + ‖s‖ ^ 2) * ((a + b).factorial : ℝ)) * Real.exp (-Real.pi * ‖s‖ ^ 2) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = _ := by
          rw [show -(Real.pi - 1) * ‖s‖ ^ 2 = ‖s‖ ^ 2 + -Real.pi * ‖s‖ ^ 2 by ring,
            Real.exp_add, Real.exp_add]
          ring

/- English proof (translation)
Unfold `HasLineDerivAt`. Establish `h1 : HasDerivAt (fun t : ℂ => s + t * v) v 0`. Simplify using `using ((hasDerivAt_id (0 : ℂ)).mul_const v).const_add s`. Establish `h2 : HasDerivAt (fun t : ℂ => starRingEnd ℂ s + t * starRingEnd ℂ v) (starRingEnd ℂ v) 0`. Simplify using `using ((hasDerivAt_id (0 : ℂ)).mul_const (starRingEnd ℂ v)).const_add (starRingEnd ℂ s)`.

Establish `h3` using `(h2.fun_pow k).fun_mul ((((h1.fun_mul h2).const_mul (-(Real.pi : ℂ))).fun_sub (((h1.mul_const y).fun_add (h2.mul_const (starRingEnd ℂ y))).const_mul ((Real.pi : ℂ) * Complex.I))).cexp)`. Establish `h4` using `HasDerivAt.comp_ofReal (z := 0) (by simpa using h3)`. Use `convert! h4 using 1`. Use function extensionality and compare the values at `t`. Simplify using `[gE]`.

Simplify using `only [gE, neg_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma gE_deriv (y : ℂ) (k : ℕ) (v s : ℂ) :
    HasLineDerivAt ℝ (fun s : ℂ => (starRingEnd ℂ s) ^ k * gE y s)
      (v * (-(Real.pi : ℂ) * (s ^ 0 * (starRingEnd ℂ s) ^ (k + 1) * gE y s)
          - (Real.pi : ℂ) * Complex.I * y * (s ^ 0 * (starRingEnd ℂ s) ^ k * gE y s)) +
        starRingEnd ℂ v * ((k : ℂ) * (s ^ 0 * (starRingEnd ℂ s) ^ (k - 1) * gE y s)
          - (Real.pi : ℂ) * (s ^ 1 * (starRingEnd ℂ s) ^ k * gE y s)
          - (Real.pi : ℂ) * Complex.I * starRingEnd ℂ y * (s ^ 0 * (starRingEnd ℂ s) ^ k * gE y s)))
      s v := by
  unfold HasLineDerivAt
  have h1 : HasDerivAt (fun t : ℂ => s + t * v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const v).const_add s
  have h2 : HasDerivAt (fun t : ℂ => starRingEnd ℂ s + t * starRingEnd ℂ v) (starRingEnd ℂ v) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (starRingEnd ℂ v)).const_add (starRingEnd ℂ s)
  have h3 := (h2.fun_pow k).fun_mul ((((h1.fun_mul h2).const_mul (-(Real.pi : ℂ))).fun_sub
    (((h1.mul_const y).fun_add (h2.mul_const (starRingEnd ℂ y))).const_mul
      ((Real.pi : ℂ) * Complex.I))).cexp)
  have h4 := HasDerivAt.comp_ofReal (z := 0) (by simpa using h3)
  convert! h4 using 1
  · funext t
    simp [gE]
  · simp only [gE, neg_mul]
    ring

/- English proof (translation)
Establish `i1` using `(gE_int y 0 (k + 1)).const_mul (-(Real.pi : ℂ))`. Establish `i2` using `(gE_int y 0 k).const_mul ((Real.pi : ℂ) * Complex.I * y)`. Establish `i3` using `(gE_int y 0 (k - 1)).const_mul (k : ℂ)`. Establish `i4` using `(gE_int y 1 k).const_mul (Real.pi : ℂ)`. Establish `i5` using `(gE_int y 0 k).const_mul ((Real.pi : ℂ) * Complex.I * starRingEnd ℂ y)`.

Establish `j1` using `(i1.sub' i2).const_mul v`. Establish `j2` using `((i3.sub' i4).sub' i5).const_mul (starRingEnd ℂ v)`. Establish `H` using `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume) (f := fun _ : ℂ => (1 : ℂ)) (f' := fun _ => 0) (v := v) (B := ContinuousLinearMap.mul ℝ ℂ) (g := fun s : ℂ => (starRingEnd ℂ s) ^ k * gE y s) (by simp) ?_ ?_ ?_ (fun s _ => gE_deriv y k v s)`. Simplify using `only [ContinuousLinearMap.mul_apply', one_mul, zero_mul, integral_zero, neg_zero] at H`. Rewrite `H` using `[integral_add j1 j2, integral_const_mul, integral_const_mul, integral_sub i1 i2, integral_sub (i3.sub' i4) i5, integral_sub i3 i4]`.

Simplify using `only [integral_const_mul] at H`. Conclude with `H`. Simplify using `only [ContinuousLinearMap.mul_apply', one_mul]`. Conclude with `j1.add j2`. Simplify using `using gE_int y 0 k`.

Introduce `x _`. Conclude with `(hasFDerivAt_const (1 : ℂ) x).hasLineDerivAt v`.
-/
private lemma gE_zero (y : ℂ) (k : ℕ) (v : ℂ) :
    v * (-(Real.pi : ℂ) * (∫ s : ℂ, s ^ 0 * (starRingEnd ℂ s) ^ (k + 1) * gE y s)
          - (Real.pi : ℂ) * Complex.I * y * (∫ s : ℂ, s ^ 0 * (starRingEnd ℂ s) ^ k * gE y s)) +
        starRingEnd ℂ v * ((k : ℂ) * (∫ s : ℂ, s ^ 0 * (starRingEnd ℂ s) ^ (k - 1) * gE y s)
          - (Real.pi : ℂ) * (∫ s : ℂ, s ^ 1 * (starRingEnd ℂ s) ^ k * gE y s)
          - (Real.pi : ℂ) * Complex.I * starRingEnd ℂ y *
            (∫ s : ℂ, s ^ 0 * (starRingEnd ℂ s) ^ k * gE y s)) = 0 := by
  have i1 := (gE_int y 0 (k + 1)).const_mul (-(Real.pi : ℂ))
  have i2 := (gE_int y 0 k).const_mul ((Real.pi : ℂ) * Complex.I * y)
  have i3 := (gE_int y 0 (k - 1)).const_mul (k : ℂ)
  have i4 := (gE_int y 1 k).const_mul (Real.pi : ℂ)
  have i5 := (gE_int y 0 k).const_mul ((Real.pi : ℂ) * Complex.I * starRingEnd ℂ y)
  have j1 := (i1.sub' i2).const_mul v
  have j2 := ((i3.sub' i4).sub' i5).const_mul (starRingEnd ℂ v)
  have H := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (f := fun _ : ℂ => (1 : ℂ)) (f' := fun _ => 0) (v := v) (B := ContinuousLinearMap.mul ℝ ℂ)
    (g := fun s : ℂ => (starRingEnd ℂ s) ^ k * gE y s) (by simp) ?_ ?_ ?_
    (fun s _ => gE_deriv y k v s)
  · simp only [ContinuousLinearMap.mul_apply', one_mul, zero_mul, integral_zero, neg_zero] at H
    rw [integral_add j1 j2, integral_const_mul, integral_const_mul, integral_sub i1 i2,
      integral_sub (i3.sub' i4) i5, integral_sub i3 i4] at H
    simp only [integral_const_mul] at H
    exact H
  · simp only [ContinuousLinearMap.mul_apply', one_mul]
    exact j1.add j2
  · simpa using gE_int y 0 k
  · intro x _
    exact (hasFDerivAt_const (1 : ℂ) x).hasLineDerivAt v

/- English proof (translation)
Introduce `k y`. Simplify using `only [mul_assoc _ (Complex.exp _) (Complex.exp _), ← gE_eq]`. Proceed by induction on `k with`. Consider the case `zero`. Establish `hb : 0 < ((Real.pi : ℝ) : ℂ).re`.

Rewrite using `[Complex.ofReal_re]`. Conclude with `Real.pi_pos`. Establish `h` using `GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := ℂ) hb (-(2 * Real.pi * Complex.I)) (starRingEnd ℂ y)`. Establish `hp : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Simplify using `only [pow_zero, one_mul, gE_eq, ← Complex.exp_add]`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use `congr 1`. Use function extensionality and compare the values at `s`. Simplify using `[Complex.inner, mul_comm]`. Rewrite using `[div_self hp, Complex.one_cpow, one_mul, Complex.norm_conj]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Establish `h1` using `gE_zero y k 1`. Establish `h2` using `gE_zero y k Complex.I`. Establish `hp : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Simplify using `only [pow_zero, one_mul, map_one, Complex.conj_I, ih] at h1 h2`. Apply `mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero hp) Complex.I_ne_zero)` to reduce the goal to its premises.

Take the linear combination `-Complex.I * h1 - h2`.
-/
theorem UpperTheory.gaussian_fourier_conj_power :
    ∀ (k : ℕ) (y : ℂ), ∫ s : ℂ, (starRingEnd ℂ s) ^ k * Complex.exp (-(Real.pi : ℂ) * (‖s‖ : ℂ) ^ 2) *
          Complex.exp (-(2 * Real.pi * Complex.I) * (((s * y).re : ℝ) : ℂ)) =
        (-Complex.I * y) ^ k * Complex.exp (-(Real.pi : ℂ) * (‖y‖ : ℂ) ^ 2) := by
  intro k y
  simp only [mul_assoc _ (Complex.exp _) (Complex.exp _), ← gE_eq]
  induction k with
  | zero =>
    have hb : 0 < ((Real.pi : ℝ) : ℂ).re := by
      rw [Complex.ofReal_re]; exact Real.pi_pos
    have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := ℂ) hb
      (-(2 * Real.pi * Complex.I)) (starRingEnd ℂ y)
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [pow_zero, one_mul, gE_eq, ← Complex.exp_add]
    convert h using 1
    · congr 1
      funext s
      simp [Complex.inner, mul_comm]
    · rw [div_self hp, Complex.one_cpow, one_mul, Complex.norm_conj]
      congr 1
      field_simp
      ring_nf
      simp
  | succ k ih =>
    have h1 := gE_zero y k 1
    have h2 := gE_zero y k Complex.I
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [pow_zero, one_mul, map_one, Complex.conj_I, ih] at h1 h2
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero hp) Complex.I_ne_zero)
    linear_combination -Complex.I * h1 - h2
