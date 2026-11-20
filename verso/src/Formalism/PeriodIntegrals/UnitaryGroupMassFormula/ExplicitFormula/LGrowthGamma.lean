import Mathlib

noncomputable section

namespace PI.EF

open Complex Filter Set

/- English proof (translation)
Rewrite using `[Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw, Complex.GammaIntegral]`. Use `(MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)` and prove the remaining obligations. Apply `MeasureTheory.setIntegral_congr_fun measurableSet_Ioi` to reduce the goal to its premises. Introduce `x hx`. Establish `hx' : 0 < x` using `hx`.

Simplify using `only`. Rewrite using `[norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx', Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`. Simplify using the standard rewrite rules.
-/
theorem norm_Gamma_le {w : ℂ} (hw : 0 < w.re) : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw, Complex.GammaIntegral]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx' : 0 < x := hx
  simp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx', Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simp

/- English proof (translation)
Establish `h : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2`. Rewrite using `[Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]`. Use `sq_le_sq.mpr h1` as an intermediate fact. Use `sq_le_sq.mpr h2` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg a) (norm_nonneg b) two_ne_zero).mp h`.
-/
theorem norm_le_norm_of {a b : ℂ} (h1 : |a.re| ≤ |b.re|) (h2 : |a.im| ≤ |b.im|) : ‖a‖ ≤ ‖b‖ := by
  have h : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    have := sq_le_sq.mpr h1
    have := sq_le_sq.mpr h2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg a) (norm_nonneg b) two_ne_zero).mp h

/- English proof (translation)
Use `set z : ℂ := 1 / 2 + t * I with hz`. Establish `hconj : 1 - z = (starRingEnd ℂ) z`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[hz]`. Evaluate the numerical expressions.

Simplify using `[hz]`. Establish `h` using `Complex.Gamma_mul_Gamma_one_sub z`. Rewrite `h` using `[hconj, Complex.Gamma_conj, Complex.mul_conj]`. Establish `hs : Complex.sin (Real.pi * z) = ((Real.cosh (Real.pi * t) : ℝ) : ℂ)`. Establish `e : (Real.pi : ℂ) * z = ((Real.pi * t : ℝ) : ℂ) * I + Real.pi / 2`.

Rewrite using `[hz]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]`. Rewrite `h` using `[hs]`.

Establish `h' : normSq (Complex.Gamma z) = Real.pi / Real.cosh (Real.pi * t)` using `by exact_mod_cast h`. Rewrite using `[← h', Complex.normSq_eq_norm_sq]`.
-/
theorem norm_sq_Gamma_half (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  set z : ℂ := 1 / 2 + t * I with hz
  have hconj : 1 - z = (starRingEnd ℂ) z := by
    apply Complex.ext
    · simp [hz]; norm_num
    · simp [hz]
  have h := Complex.Gamma_mul_Gamma_one_sub z
  rw [hconj, Complex.Gamma_conj, Complex.mul_conj] at h
  have hs : Complex.sin (Real.pi * z) = ((Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    have e : (Real.pi : ℂ) * z = ((Real.pi * t : ℝ) : ℂ) * I + Real.pi / 2 := by
      rw [hz]; push_cast; ring
    rw [e, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [hs] at h
  have h' : normSq (Complex.Gamma z) = Real.pi / Real.cosh (Real.pi * t) := by exact_mod_cast h
  rw [← h', Complex.normSq_eq_norm_sq]

/- English proof (translation)
Establish `h` using `norm_sq_Gamma_half t`. Establish `hpi` using `Real.pi_pos`. Establish `hc : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * t)`. Rewrite using `[← Real.cosh_abs, abs_mul, abs_of_pos hpi, Real.cosh_eq]`. Use `Real.exp_pos (-(Real.pi * |t|))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `he : Real.exp (Real.pi / 2 * |t|) ^ 2 = Real.exp (Real.pi * |t|)`. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hE` using `Real.exp_pos (Real.pi * |t|)`. Establish `hsq : (‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (Real.pi / 2 * |t|)) ^ 2 ≤ 9`. Rewrite using `[mul_pow, h, he, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]`. Use `Real.pi_lt_four` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `h0 : 0 ≤ ‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (Real.pi / 2 * |t|)` using `by positivity`. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_le]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem half_line (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (Real.pi / 2 * |t|) ≤ 3 := by
  have h := norm_sq_Gamma_half t
  have hpi := Real.pi_pos
  have hc : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * t) := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos hpi, Real.cosh_eq]
    have := Real.exp_pos (-(Real.pi * |t|))
    linarith
  have he : Real.exp (Real.pi / 2 * |t|) ^ 2 = Real.exp (Real.pi * |t|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hE := Real.exp_pos (Real.pi * |t|)
  have hsq : (‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (Real.pi / 2 * |t|)) ^ 2 ≤ 9 := by
    rw [mul_pow, h, he, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have := Real.pi_lt_four
    nlinarith
  have h0 : 0 ≤ ‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (Real.pi / 2 * |t|) := by positivity
  by_contra hcon
  rw [not_le] at hcon
  nlinarith

def frobeniusStickelbergerDetMulSigmaCube (w : ℂ) : ℂ := Complex.Gamma w * Complex.exp (-(Real.pi / 2) * I * w) / (w + 1) ^ 5

/- English proof (translation)
Unfold `frobeniusStickelbergerDetMulSigmaCube`. Rewrite using `[norm_div, norm_mul, norm_pow, Complex.norm_exp]`. Use `congr 3`. Simplify using the standard rewrite rules.
-/
theorem norm_twistedGamma (w : ℂ) :
    ‖frobeniusStickelbergerDetMulSigmaCube w‖ = ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * w.im) / ‖w + 1‖ ^ 5 := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  rw [norm_div, norm_mul, norm_pow, Complex.norm_exp]
  congr 3
  simp

/- English proof (translation)
Establish `h` using `Complex.abs_re_le_norm (w + 1)`. Establish `: |(w + 1).re| = w.re + 1`. Rewrite using `[Complex.add_re, Complex.one_re, abs_of_nonneg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_norm_add_one {w : ℂ} (hw : 0 ≤ w.re) : 1 ≤ ‖w + 1‖ := by
  have h := Complex.abs_re_le_norm (w + 1)
  have : |(w + 1).re| = w.re + 1 := by
    rw [Complex.add_re, Complex.one_re, abs_of_nonneg (by linarith)]
  linarith

/- English proof (translation)
The claim follows from `(Complex.re_add_im w).symm`.
-/
theorem eq_re_add_im (w : ℂ) : w = (w.re : ℂ) + w.im * I := (Complex.re_add_im w).symm

/- English proof (translation)
Rewrite using `[norm_twistedGamma]`. Establish `h1` using `one_le_norm_add_one (w := w) (by rw [hw]; norm_num)`. Establish `e : w = 1 / 2 + (w.im : ℂ) * I` using `by conv_lhs => rw [eq_re_add_im w, hw]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2` using `half_line w.im`. Rewrite `h2` using `[← e]`. Establish `h3 : Real.exp (Real.pi / 2 * w.im) ≤ Real.exp (Real.pi / 2 * |w.im|)` using `Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))`. Establish `h4 : (1 : ℝ) ≤ ‖w + 1‖ ^ 5` using `one_le_pow₀ h1`. Rewrite using `[div_le_iff₀ (by linarith)]`.

Establish `h5 : ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * w.im) ≤ 3` using `(mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans h2`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_twistedGamma_le_of_re_eq_half (w : ℂ) (hw : w.re = 1 / 2) : ‖frobeniusStickelbergerDetMulSigmaCube w‖ ≤ 3 := by
  rw [norm_twistedGamma]
  have h1 := one_le_norm_add_one (w := w) (by rw [hw]; norm_num)
  have e : w = 1 / 2 + (w.im : ℂ) * I := by
    conv_lhs => rw [eq_re_add_im w, hw]
    push_cast
    ring
  have h2 := half_line w.im
  rw [← e] at h2
  have h3 : Real.exp (Real.pi / 2 * w.im) ≤ Real.exp (Real.pi / 2 * |w.im|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
  have h4 : (1 : ℝ) ≤ ‖w + 1‖ ^ 5 := one_le_pow₀ h1
  rw [div_le_iff₀ (by linarith)]
  have h5 : ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * w.im) ≤ 3 :=
    (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans h2
  nlinarith

/- English proof (translation)
Establish `ne : ∀ k : ℕ, z + k ≠ 0`. Introduce `k h`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`. Establish `hk : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0` using `Complex.Gamma_add_one z (by simpa using ne 0)`. Establish `h1` using `Complex.Gamma_add_one (z + 1) (by simpa using ne 1)`. Establish `h2` using `Complex.Gamma_add_one (z + 2) (by simpa using ne 2)`. Establish `h3` using `Complex.Gamma_add_one (z + 3) (by simpa using ne 3)`.

Establish `h4` using `Complex.Gamma_add_one (z + 4) (by simpa using ne 4)`. Rewrite using `[show z + 5 = z + 4 + 1 by ring, h4, show z + 4 = z + 3 + 1 by ring, h3, show z + 3 = z + 2 + 1 by ring, h2, show z + 2 = z + 1 + 1 by ring, h1, h0]`.
-/
theorem Gamma_add_five (z : ℂ) (hz : 0 < z.re) :
    Complex.Gamma (z + 5) = (z + 4) * ((z + 3) * ((z + 2) * ((z + 1) * (z * Complex.Gamma z)))) := by
  have ne : ∀ k : ℕ, z + k ≠ 0 := by
    intro k h
    have := congrArg Complex.re h
    simp at this
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have h0 := Complex.Gamma_add_one z (by simpa using ne 0)
  have h1 := Complex.Gamma_add_one (z + 1) (by simpa using ne 1)
  have h2 := Complex.Gamma_add_one (z + 2) (by simpa using ne 2)
  have h3 := Complex.Gamma_add_one (z + 3) (by simpa using ne 3)
  have h4 := Complex.Gamma_add_one (z + 4) (by simpa using ne 4)
  rw [show z + 5 = z + 4 + 1 by ring, h4, show z + 4 = z + 3 + 1 by ring, h3,
    show z + 3 = z + 2 + 1 by ring, h2, show z + 2 = z + 1 + 1 by ring, h1, h0]

/- English proof (translation)
Rewrite using `[norm_twistedGamma]`. Establish `h1` using `one_le_norm_add_one (w := w) (by rw [hw]; norm_num)`. Use `set z : ℂ := 1 / 2 + (w.im : ℂ) * I with hz`. Establish `e : w = z + 5` using `by conv_lhs => rw [eq_re_add_im w, hw]`. Rewrite using `[hz]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hzre : z.re = 1 / 2` using `by simp [hz]`. Establish `hzim : z.im = w.im` using `by simp [hz]`. Establish `h2` using `half_line w.im`.

Rewrite `h2` using `[← hz]`. Establish `h3 : Real.exp (Real.pi / 2 * w.im) ≤ Real.exp (Real.pi / 2 * |w.im|)` using `Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))`. Establish `hb : ∀ k : ℝ, 0 ≤ k → k ≤ 4 → ‖z + (k : ℂ)‖ ≤ ‖w + 1‖`. Introduce `k hk0 hk4`. Apply `norm_le_norm_of` to reduce the goal to its premises.

Simplify using `only [Complex.add_re, Complex.ofReal_re, Complex.one_re, hzre, hw]`. Rewrite using `[abs_of_nonneg (by linarith), abs_of_nonneg (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[hzim]`. Establish `b0 : ‖z‖ ≤ ‖w + 1‖` using `by simpa using hb 0 (le_refl _) (by norm_num)`.

Establish `b1 : ‖z + 1‖ ≤ ‖w + 1‖` using `by simpa using hb 1 (by norm_num) (by norm_num)`. Establish `b2 : ‖z + 2‖ ≤ ‖w + 1‖` using `by simpa using hb 2 (by norm_num) (by norm_num)`. Establish `b3 : ‖z + 3‖ ≤ ‖w + 1‖` using `by simpa using hb 3 (by norm_num) (by norm_num)`. Establish `b4 : ‖z + 4‖ ≤ ‖w + 1‖` using `by simpa using hb 4 (by norm_num) (by norm_num)`. Establish `hG : ‖Complex.Gamma w‖ ≤ ‖w + 1‖ ^ 5 * ‖Complex.Gamma z‖`.

Rewrite using `[e, Gamma_add_five z (by rw [hzre]; norm_num), ← e]`. Simplify using `only [norm_mul]`. Use `set X := ‖w + 1‖`. Establish `hX : 0 ≤ X` using `norm_nonneg _`. Establish `hg` using `norm_nonneg (Complex.Gamma z)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hpos : 0 < ‖w + 1‖ ^ 5` using `by positivity`. Rewrite using `[div_le_iff₀ hpos]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_twistedGamma_le_of_re_eq_eleven_halves (w : ℂ) (hw : w.re = 11 / 2) : ‖frobeniusStickelbergerDetMulSigmaCube w‖ ≤ 3 := by
  rw [norm_twistedGamma]
  have h1 := one_le_norm_add_one (w := w) (by rw [hw]; norm_num)
  set z : ℂ := 1 / 2 + (w.im : ℂ) * I with hz
  have e : w = z + 5 := by
    conv_lhs => rw [eq_re_add_im w, hw]
    rw [hz]
    push_cast
    ring
  have hzre : z.re = 1 / 2 := by simp [hz]
  have hzim : z.im = w.im := by simp [hz]
  have h2 := half_line w.im
  rw [← hz] at h2
  have h3 : Real.exp (Real.pi / 2 * w.im) ≤ Real.exp (Real.pi / 2 * |w.im|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
  have hb : ∀ k : ℝ, 0 ≤ k → k ≤ 4 → ‖z + (k : ℂ)‖ ≤ ‖w + 1‖ := by
    intro k hk0 hk4
    apply norm_le_norm_of
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re, hzre, hw]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by norm_num)]
      linarith
    · simp [hzim]
  have b0 : ‖z‖ ≤ ‖w + 1‖ := by simpa using hb 0 (le_refl _) (by norm_num)
  have b1 : ‖z + 1‖ ≤ ‖w + 1‖ := by simpa using hb 1 (by norm_num) (by norm_num)
  have b2 : ‖z + 2‖ ≤ ‖w + 1‖ := by simpa using hb 2 (by norm_num) (by norm_num)
  have b3 : ‖z + 3‖ ≤ ‖w + 1‖ := by simpa using hb 3 (by norm_num) (by norm_num)
  have b4 : ‖z + 4‖ ≤ ‖w + 1‖ := by simpa using hb 4 (by norm_num) (by norm_num)
  have hG : ‖Complex.Gamma w‖ ≤ ‖w + 1‖ ^ 5 * ‖Complex.Gamma z‖ := by
    rw [e, Gamma_add_five z (by rw [hzre]; norm_num), ← e]
    simp only [norm_mul]
    set X := ‖w + 1‖
    have hX : 0 ≤ X := norm_nonneg _
    have hg := norm_nonneg (Complex.Gamma z)
    calc ‖z + 4‖ * (‖z + 3‖ * (‖z + 2‖ * (‖z + 1‖ * (‖z‖ * ‖Complex.Gamma z‖))))
        ≤ X * (X * (X * (X * (X * ‖Complex.Gamma z‖)))) := by gcongr
      _ = X ^ 5 * ‖Complex.Gamma z‖ := by ring
  have hpos : 0 < ‖w + 1‖ ^ 5 := by positivity
  rw [div_le_iff₀ hpos]
  calc ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * w.im)
      ≤ (‖w + 1‖ ^ 5 * ‖Complex.Gamma z‖) * Real.exp (Real.pi / 2 * |w.im|) :=
        mul_le_mul hG h3 (Real.exp_pos _).le (by positivity)
    _ = (‖Complex.Gamma z‖ * Real.exp (Real.pi / 2 * |w.im|)) * ‖w + 1‖ ^ 5 := by ring
    _ ≤ 3 * ‖w + 1‖ ^ 5 := mul_le_mul_of_nonneg_right h2 hpos.le

/- English proof (translation)
Apply `DifferentiableOn.diffContOnCl` to reduce the goal to its premises. Establish `hcl : closure (re ⁻¹' Ioo (1 / 2 : ℝ) (11 / 2)) ⊆ re ⁻¹' Icc (1 / 2 : ℝ) (11 / 2)` using `closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage Complex.continuous_re)`. Introduce `w hw`. Establish `hw'` using `hcl hw`. Establish `hre : (1 / 2 : ℝ) ≤ w.re` using `hw'.1`.

Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Unfold `frobeniusStickelbergerDetMulSigmaCube`. Apply `DifferentiableAt.div` to reduce the goal to its premises. Apply `DifferentiableAt.mul` to reduce the goal to its premises. Apply `Complex.differentiableAt_Gamma` to reduce the goal to its premises.

Introduce `m h`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`. Establish `hm : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `fun_prop`. Use `fun_prop`. Apply `pow_ne_zero` to reduce the goal to its premises. Introduce `h`. Use `congrArg Complex.re h` as an intermediate fact.

Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem diffContOnCl_twistedGamma : DiffContOnCl ℂ frobeniusStickelbergerDetMulSigmaCube (re ⁻¹' Ioo (1 / 2 : ℝ) (11 / 2)) := by
  apply DifferentiableOn.diffContOnCl
  have hcl : closure (re ⁻¹' Ioo (1 / 2 : ℝ) (11 / 2)) ⊆ re ⁻¹' Icc (1 / 2 : ℝ) (11 / 2) :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage Complex.continuous_re)
  intro w hw
  have hw' := hcl hw
  have hre : (1 / 2 : ℝ) ≤ w.re := hw'.1
  apply DifferentiableAt.differentiableWithinAt
  unfold frobeniusStickelbergerDetMulSigmaCube
  apply DifferentiableAt.div
  · apply DifferentiableAt.mul
    · apply Complex.differentiableAt_Gamma
      intro m h
      have := congrArg Complex.re h
      simp at this
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · fun_prop
  · fun_prop
  · apply pow_ne_zero
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith

/- English proof (translation)
Use `PhragmenLindelof.vertical_strip diffContOnCl_twistedGamma ?_ norm_twistedGamma_le_of_re_eq_half norm_twistedGamma_le_of_re_eq_eleven_halves h1 h2` and prove the remaining obligations. Use `⟨1 / 2, ?_, Real.pi, ?_⟩` and prove the remaining obligations. Use `Real.pi_gt_three` as an intermediate fact. Rewrite using `[lt_div_iff₀ (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Apply `Asymptotics.IsBigO.of_bound (max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)))` to reduce the goal to its premises. Apply `Filter.eventually_inf_principal.mpr` to reduce the goal to its premises. Apply `Filter.Eventually.of_forall` to reduce the goal to its premises. Introduce `z hz`. Establish `hz1 : (1 / 2 : ℝ) < z.re` using `hz.1`.

Establish `hz2 : z.re < 11 / 2` using `hz.2`. Rewrite using `[norm_twistedGamma, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`. Establish `a1 : ‖Complex.Gamma z‖ ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2))` using `(norm_Gamma_le (by linarith)).trans (Real.convexOn_Gamma.le_max_of_mem_Icc (by norm_num [Set.mem_Ioi]) (by norm_num [Set.mem_Ioi]) ⟨hz1.le, hz2.le⟩)`. Establish `a2 : Real.exp (Real.pi / 2 * z.im) ≤ Real.exp (Real.pi * Real.exp (1 / 2 * |z.im|))`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Establish `q1` using `Real.add_one_le_exp (1 / 2 * |z.im|)`. Establish `q2` using `le_abs_self z.im`. Establish `q3` using `abs_nonneg z.im`. Establish `hpi` using `Real.pi_pos`. Use the polynomial consequences of the given equalities and inequalities.

Establish `a3 : (1 : ℝ) ≤ ‖z + 1‖ ^ 5` using `one_le_pow₀ (one_le_norm_add_one (by linarith))`. Rewrite using `[div_le_iff₀ (by linarith)]`. Establish `a4 : 0 ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2))` using `(norm_nonneg _).trans a1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_twistedGamma_le {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 11 / 2) : ‖frobeniusStickelbergerDetMulSigmaCube w‖ ≤ 3 := by
  refine PhragmenLindelof.vertical_strip diffContOnCl_twistedGamma ?_ norm_twistedGamma_le_of_re_eq_half norm_twistedGamma_le_of_re_eq_eleven_halves h1 h2
  refine ⟨1 / 2, ?_, Real.pi, ?_⟩
  · have := Real.pi_gt_three
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  · apply Asymptotics.IsBigO.of_bound (max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)))
    apply Filter.eventually_inf_principal.mpr
    apply Filter.Eventually.of_forall
    intro z hz
    have hz1 : (1 / 2 : ℝ) < z.re := hz.1
    have hz2 : z.re < 11 / 2 := hz.2
    rw [norm_twistedGamma, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have a1 : ‖Complex.Gamma z‖ ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)) :=
      (norm_Gamma_le (by linarith)).trans
        (Real.convexOn_Gamma.le_max_of_mem_Icc (by norm_num [Set.mem_Ioi]) (by norm_num [Set.mem_Ioi])
          ⟨hz1.le, hz2.le⟩)
    have a2 : Real.exp (Real.pi / 2 * z.im) ≤ Real.exp (Real.pi * Real.exp (1 / 2 * |z.im|)) := by
      apply Real.exp_le_exp.mpr
      have q1 := Real.add_one_le_exp (1 / 2 * |z.im|)
      have q2 := le_abs_self z.im
      have q3 := abs_nonneg z.im
      have hpi := Real.pi_pos
      nlinarith
    have a3 : (1 : ℝ) ≤ ‖z + 1‖ ^ 5 := one_le_pow₀ (one_le_norm_add_one (by linarith))
    rw [div_le_iff₀ (by linarith)]
    have a4 : 0 ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)) := (norm_nonneg _).trans a1
    calc ‖Complex.Gamma z‖ * Real.exp (Real.pi / 2 * z.im)
        ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)) *
            Real.exp (Real.pi * Real.exp (1 / 2 * |z.im|)) :=
          mul_le_mul a1 a2 (Real.exp_pos _).le a4
      _ ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)) *
            Real.exp (Real.pi * Real.exp (1 / 2 * |z.im|)) * ‖z + 1‖ ^ 5 :=
          le_mul_of_one_le_right (mul_nonneg a4 (Real.exp_pos _).le) a3

/- English proof (translation)
Establish `key : ∀ v : ℂ, 1 / 2 ≤ v.re → v.re ≤ 11 / 2 → ‖Complex.Gamma v‖ * Real.exp (Real.pi / 2 * v.im) ≤ 3 * ‖v + 1‖ ^ 5`. Introduce `v a b`. Establish `h` using `norm_twistedGamma_le a b`. Rewrite using `[norm_twistedGamma, div_le_iff₀ (by`. Use `one_le_norm_add_one (w := v) (by linarith)` as an intermediate fact.

Use the proof step `positivity)] at h`. Conclude with `h`. Break down `le_total 0 w.im with hi | hi` into its components or cases. Rewrite using `[abs_of_nonneg hi]`. Conclude with `key w h1 h2`.

Rewrite using `[abs_of_nonpos hi]`. Establish `h` using `key ((starRingEnd ℂ) w) (by simpa using h1) (by simpa using h2)`. Rewrite `h` using `[Complex.Gamma_conj, Complex.norm_conj, Complex.conj_im]`. Establish `e : ‖(starRingEnd ℂ) w + 1‖ = ‖w + 1‖`. Rewrite using `[← Complex.norm_conj (w + 1), map_add, map_one]`.

Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem Gamma_decay {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 11 / 2) :
    ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * |w.im|) ≤ 3 * ‖w + 1‖ ^ 5 := by
  have key : ∀ v : ℂ, 1 / 2 ≤ v.re → v.re ≤ 11 / 2 →
      ‖Complex.Gamma v‖ * Real.exp (Real.pi / 2 * v.im) ≤ 3 * ‖v + 1‖ ^ 5 := by
    intro v a b
    have h := norm_twistedGamma_le a b
    rw [norm_twistedGamma, div_le_iff₀ (by
      have := one_le_norm_add_one (w := v) (by linarith)
      positivity)] at h
    exact h
  rcases le_total 0 w.im with hi | hi
  · rw [abs_of_nonneg hi]
    exact key w h1 h2
  · rw [abs_of_nonpos hi]
    have h := key ((starRingEnd ℂ) w) (by simpa using h1) (by simpa using h2)
    rw [Complex.Gamma_conj, Complex.norm_conj, Complex.conj_im] at h
    have e : ‖(starRingEnd ℂ) w + 1‖ = ‖w + 1‖ := by
      rw [← Complex.norm_conj (w + 1), map_add, map_one]
    rw [e] at h
    exact h

end PI.EF
