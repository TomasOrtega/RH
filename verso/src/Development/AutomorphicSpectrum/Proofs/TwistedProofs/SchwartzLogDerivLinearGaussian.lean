import Mathlib

namespace GlobalTheory.CompanionTheory.Twist

/- English proof (translation)
Establish `hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f₀ (s • y)) ((t : ℂ) * m y y * f₀ (t • y)) t`. Introduce `t`. Establish `h1 : HasFDerivAt f₀ (fderiv ℝ f₀ (t • y)) (t • y)` using `f₀.differentiableAt.hasFDerivAt`. Establish `h2 : HasDerivAt (fun s : ℝ => s • y) y t`. Simplify using `using (hasDerivAt_id t).smul_const y`.

Establish `h3 : HasDerivAt (fun s : ℝ => f₀ (s • y)) (fderiv ℝ f₀ (t • y) y) t` using `h1.comp_hasDerivAt t h2`. Rewrite `h3` using `[hm, map_smul, Complex.real_smul]`. Conclude with `h3`. Establish `hE : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) ^ 2 * m y y / 2))) (Complex.exp (-((t : ℂ) ^ 2 * m y y / 2)) * (-((t : ℂ) * m y y))) t`. Introduce `t`.

Establish `h5 : HasDerivAt (fun z : ℂ => -(z ^ 2 * m y y / 2)) (-((t : ℂ) * m y y)) (t : ℂ)`. Establish `h6` using `(((hasDerivAt_pow 2 (t : ℂ)).mul_const (m y y)).div_const 2).neg`. Use `h6.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[show (2 : ℕ) - 1 = 1 from rfl, pow_one]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `h5.cexp.comp_ofReal`. Establish `hH : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f₀ (s • y) * Complex.exp (-((s : ℂ) ^ 2 * m y y / 2))) 0 t`. Introduce `t`. Use `((hg t).mul (hE t)).congr_deriv ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `h10` using `is_const_of_deriv_eq_zero (fun t => (hH t).differentiableAt) (fun t => (hH t).deriv) 1 0`. Simplify using `only [one_smul, zero_smul, Complex.ofReal_one, Complex.ofReal_zero, one_pow, one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div, neg_zero, Complex.exp_zero, mul_one] at h10`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]`.

Use `_ = f₀ 0 * Complex.exp (m y y / 2) := by rw [h10]`.
-/
theorem schwartz_logDeriv_linear_formula {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : SchwartzMap V ℂ) (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hm : ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y) (y : V) :
    f₀ y = f₀ 0 * Complex.exp (m y y / 2) := by
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f₀ (s • y)) ((t : ℂ) * m y y * f₀ (t • y)) t := by
    intro t
    have h1 : HasFDerivAt f₀ (fderiv ℝ f₀ (t • y)) (t • y) := f₀.differentiableAt.hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => s • y) y t := by
      simpa using (hasDerivAt_id t).smul_const y
    have h3 : HasDerivAt (fun s : ℝ => f₀ (s • y)) (fderiv ℝ f₀ (t • y) y) t :=
      h1.comp_hasDerivAt t h2
    rw [hm, map_smul, Complex.real_smul] at h3
    exact h3
  have hE : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) ^ 2 * m y y / 2)))
      (Complex.exp (-((t : ℂ) ^ 2 * m y y / 2)) * (-((t : ℂ) * m y y))) t := by
    intro t
    have h5 : HasDerivAt (fun z : ℂ => -(z ^ 2 * m y y / 2)) (-((t : ℂ) * m y y)) (t : ℂ) := by
      have h6 := (((hasDerivAt_pow 2 (t : ℂ)).mul_const (m y y)).div_const 2).neg
      refine h6.congr_deriv ?_
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact h5.cexp.comp_ofReal
  have hH : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => f₀ (s • y) * Complex.exp (-((s : ℂ) ^ 2 * m y y / 2))) 0 t := by
    intro t
    refine ((hg t).mul (hE t)).congr_deriv ?_
    ring
  have h10 := is_const_of_deriv_eq_zero (fun t => (hH t).differentiableAt) (fun t => (hH t).deriv) 1 0
  simp only [one_smul, zero_smul, Complex.ofReal_one, Complex.ofReal_zero, one_pow, one_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div, neg_zero,
    Complex.exp_zero, mul_one] at h10
  calc f₀ y = f₀ y * Complex.exp (-(m y y / 2)) * Complex.exp (m y y / 2) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = f₀ 0 * Complex.exp (m y y / 2) := by rw [h10]

/- English proof (translation)
Establish `hform` using `fun y => schwartz_logDeriv_linear_formula f₀ m hm y`. Establish `hc0 : f₀ 0 ≠ 0`. Introduce `h0`. Apply `hf` to reduce the goal to its premises. Use extensionality with `x`.

Simplify using `[hform x, h0]`. Use `⟨f₀ 0, (-(1 / 2 : ℝ)) • m.compr₂ Complex.reLm, (-(1 / 2 : ℝ)) • m.compr₂ Complex.imLm, hc0, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [LinearMap.smul_apply, LinearMap.compr₂_apply, Complex.reLm_coe, smul_eq_mul]`. Assume the negation of the conclusion as `hle`.

Use `push Not at hle`. Establish `hre : 0 ≤ (m x x).re` using `by linarith`. Take `⟨C, hCpos, hC⟩` from `f₀.decay 1 0`. Establish `hxpos : 0 < ‖x‖` using `norm_pos_iff.mpr hx`. Establish `hcpos : 0 < ‖f₀ 0‖` using `norm_pos_iff.mpr hc0`.

Use `set t : ℝ := C / (‖f₀ 0‖ * ‖x‖) + 1 with ht`. Establish `htpos : 0 < t` using `by positivity`. Establish `hlow : ‖f₀ 0‖ ≤ ‖f₀ (t • x)‖`. Rewrite using `[hform (t • x), norm_mul, Complex.norm_exp]`. Apply `le_mul_of_one_le_right (norm_nonneg _)` to reduce the goal to its premises.

Apply `Real.one_le_exp` to reduce the goal to its premises. Simplify using `only [map_smul, LinearMap.smul_apply, smul_smul, Complex.div_ofNat_re, Complex.smul_re, smul_eq_mul]`. Establish `h6` using `mul_nonneg (mul_self_nonneg t) hre`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdec` using `hC (t • x)`.

Rewrite `hdec` using `[pow_one, norm_iteratedFDeriv_zero, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]`. Establish `hbig : C < t * ‖x‖ * ‖f₀ 0‖`. Establish `hne : ‖f₀ 0‖ * ‖x‖ ≠ 0` using `by positivity`. Establish `heq : t * ‖x‖ * ‖f₀ 0‖ = C + ‖x‖ * ‖f₀ 0‖`. Rewrite using `[ht]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[heq]`. Combine the linear relations using `[mul_pos hxpos hcpos]`. Establish `h7 : t * ‖x‖ * ‖f₀ 0‖ ≤ t * ‖x‖ * ‖f₀ (t • x)‖` using `mul_le_mul_of_nonneg_left hlow (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `x`. Rewrite using `[hform x]`. Use `congr 1`. Use `congr 1`. Simplify using `only [LinearMap.smul_apply, LinearMap.compr₂_apply, Complex.reLm_coe, Complex.imLm_coe, smul_eq_mul]`.

Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`.
-/
theorem schwartz_logDeriv_linear_gaussian {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (f₀ : SchwartzMap V ℂ) (hf : f₀ ≠ 0)
    (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hm : ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y) :
    ∃ (c₀ : ℂ) (Q Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), c₀ ≠ 0 ∧ (∀ x, x ≠ 0 → 0 < Q x x) ∧
      ∀ x, f₀ x = c₀ * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ)) := by
  have hform := fun y => schwartz_logDeriv_linear_formula f₀ m hm y
  have hc0 : f₀ 0 ≠ 0 := by
    intro h0
    apply hf
    ext x
    simp [hform x, h0]
  refine ⟨f₀ 0, (-(1 / 2 : ℝ)) • m.compr₂ Complex.reLm, (-(1 / 2 : ℝ)) • m.compr₂ Complex.imLm,
    hc0, ?_, ?_⟩
  · intro x hx
    simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, Complex.reLm_coe, smul_eq_mul]
    by_contra hle
    push Not at hle
    have hre : 0 ≤ (m x x).re := by linarith
    obtain ⟨C, hCpos, hC⟩ := f₀.decay 1 0
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hcpos : 0 < ‖f₀ 0‖ := norm_pos_iff.mpr hc0
    set t : ℝ := C / (‖f₀ 0‖ * ‖x‖) + 1 with ht
    have htpos : 0 < t := by positivity
    have hlow : ‖f₀ 0‖ ≤ ‖f₀ (t • x)‖ := by
      rw [hform (t • x), norm_mul, Complex.norm_exp]
      apply le_mul_of_one_le_right (norm_nonneg _)
      apply Real.one_le_exp
      simp only [map_smul, LinearMap.smul_apply, smul_smul, Complex.div_ofNat_re, Complex.smul_re,
        smul_eq_mul]
      have h6 := mul_nonneg (mul_self_nonneg t) hre
      linarith
    have hdec := hC (t • x)
    rw [pow_one, norm_iteratedFDeriv_zero, norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at hdec
    have hbig : C < t * ‖x‖ * ‖f₀ 0‖ := by
      have hne : ‖f₀ 0‖ * ‖x‖ ≠ 0 := by positivity
      have heq : t * ‖x‖ * ‖f₀ 0‖ = C + ‖x‖ * ‖f₀ 0‖ := by
        rw [ht]
        field_simp
      rw [heq]
      linarith [mul_pos hxpos hcpos]
    have h7 : t * ‖x‖ * ‖f₀ 0‖ ≤ t * ‖x‖ * ‖f₀ (t • x)‖ :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    linarith
  · intro x
    rw [hform x]
    congr 1
    congr 1
    simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, Complex.reLm_coe, Complex.imLm_coe,
      smul_eq_mul]
    apply Complex.ext <;> simp <;> ring

end GlobalTheory.CompanionTheory.Twist
