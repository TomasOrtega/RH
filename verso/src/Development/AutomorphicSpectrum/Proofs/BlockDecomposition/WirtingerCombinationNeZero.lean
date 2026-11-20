import Mathlib

namespace GlobalTheory.CompanionTheory.Unitary

/- English proof (translation)
Introduce `χ _ hmul hnorm hnt D hD β hβ`. Establish `χ0 : χ 0 = 1`. Establish `h1` using `hmul 0 0`. Rewrite `h1` using `[add_zero]`. Establish `hne : χ 0 ≠ 0`.

Introduce `h`. Establish `h2` using `hnorm 0`. Rewrite `h2` using `[h, norm_zero]`. Conclude with `zero_ne_one h2`. Conclude with `mul_left_cancel₀ hne (h1.symm.trans (mul_one (χ 0)).symm)`.

Establish `hf0 : ∀ z, χ (((0 : ℝ) : ℂ) * z) = 1`. Introduce `z`. Simplify using `[χ0]`. Establish `hre : ∀ w, (D w).re = 0`. Introduce `w`.

Establish `h1` using `(hD w).mul (hD w).star`. Establish `hconst : ((fun t : ℝ => χ (t * w)) * fun t : ℝ => star (χ (t * w))) = fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `t`. Simplify using `only [Pi.mul_apply]`. Rewrite using `[← starRingEnd_apply, RCLike.mul_conj, hnorm]`.

Simplify using the standard rewrite rules. Rewrite `h1` using `[hconst]`. Establish `h2` using `h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))`. Rewrite `h2` using `[hf0]`. Simplify using `only [star_one, mul_one, one_mul] at h2`.

Establish `h3` using `congrArg Complex.re h2`. Simplify using `only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h3`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hadd : ∀ z w, D (z + w) = D z + D w`. Introduce `z w`.

Establish `h1` using `(hD z).mul (hD w)`. Establish `hfun : ((fun t : ℝ => χ (t * z)) * fun t : ℝ => χ (t * w)) = fun t : ℝ => χ (t * (z + w))`. Use function extensionality and compare the values at `t`. Simplify using `only [Pi.mul_apply]`. Rewrite using `[mul_add, hmul]`.

Rewrite `h1` using `[hfun, hf0, hf0, mul_one, one_mul]`. Conclude with `(hD (z + w)).unique h1`. Establish `hsmul : ∀ (r : ℝ) (z : ℂ), D (r * z) = r * D z`. Introduce `r z`. Establish `hr : HasDerivAt (fun t : ℝ => r * t) r 0`.

Simplify using `using (hasDerivAt_id (0 : ℝ)).const_mul r`. Establish `hz : HasDerivAt (fun t : ℝ => χ (t * z)) (D z) ((fun t : ℝ => r * t) 0)`. Simplify using `only [mul_zero]`. Conclude with `hD z`. Establish `h1` using `HasDerivAt.scomp (h := fun t : ℝ => r * t) (0 : ℝ) hz hr`.

Establish `hfun : ((fun t : ℝ => χ (t * z)) ∘ fun t : ℝ => r * t) = fun t : ℝ => χ (t * (r * z))`. Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[hfun]`. Rewrite using `[(hD (r * z)).unique h1, Complex.real_smul]`. Establish `hzero : (∀ z, D z = 0) → False`. Introduce `h0`.

Take `⟨z, hz⟩` from `hnt`. Apply `hz` to reduce the goal to its premises. Establish `hder : ∀ s : ℝ, HasDerivAt (fun t : ℝ => χ (t * z)) 0 s`. Introduce `s`. Establish `h1 : HasDerivAt (fun t : ℝ => χ (((t - s : ℝ) : ℂ) * z)) (D z) s` using `HasDerivAt.comp_sub_const (f := fun t : ℝ => χ (t * z)) s s (by rw [sub_self]; exact hD z)`.

Establish `h2` using `h1.const_mul (χ (s * z))`. Establish `hfun : (fun t : ℝ => χ (s * z) * χ (((t - s : ℝ) : ℂ) * z)) = fun t : ℝ => χ (t * z)`. Use function extensionality and compare the values at `t`. Rewrite using `[← hmul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[hfun, h0, mul_zero]`. Conclude with `h2`. Establish `hc` using `is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt) (fun s => (hder s).deriv) 1 0`.

Simplify using `only [Complex.ofReal_one, one_mul] at hc`. Rewrite using `[hc, hf0]`. Introduce `hcomb`. Establish `ha : D β = Complex.I * D (β * Complex.I)` using `sub_eq_zero.mp hcomb`. Establish `hb0 : D (β * Complex.I) = 0`.

Apply `Complex.ext` to reduce the goal to its premises. Conclude with `hre _`. Establish `h1` using `congrArg Complex.re ha`. Simplify using `only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, hre] at h1`. Simplify using `only [Complex.zero_im]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha0 : D β = 0` using `by rw [ha, hb0, mul_zero]`. Apply `hzero` to reduce the goal to its premises. Introduce `z`. Establish `hz : z = ((z / β).re : ℂ) * β + ((z / β).im : ℂ) * (β * Complex.I)`.

Establish `e : z = (z / β) * β` using `by field_simp`. Use `conv_lhs => rw [e, ← Complex.re_add_im (z / β)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hz, hadd, hsmul, hsmul, ha0, hb0, mul_zero, mul_zero, add_zero]`.
-/
theorem wirtinger_combination_ne_zero : ∀ (χ : ℂ → ℂ), Continuous χ → (∀ z w, χ (z + w) = χ z * χ w) →
    (∀ z, ‖χ z‖ = 1) → (∃ z, χ z ≠ 1) → ∀ (D : ℂ → ℂ),
    (∀ z, HasDerivAt (fun t : ℝ => χ (t * z)) (D z) 0) →
    ∀ β : ℂ, β ≠ 0 → D β - Complex.I * D (β * Complex.I) ≠ 0 := by
  intro χ _ hmul hnorm hnt D hD β hβ
  have χ0 : χ 0 = 1 := by
    have h1 := hmul 0 0
    rw [add_zero] at h1
    have hne : χ 0 ≠ 0 := by
      intro h
      have h2 := hnorm 0
      rw [h, norm_zero] at h2
      exact zero_ne_one h2
    exact mul_left_cancel₀ hne (h1.symm.trans (mul_one (χ 0)).symm)
  have hf0 : ∀ z, χ (((0 : ℝ) : ℂ) * z) = 1 := by
    intro z
    simp [χ0]
  have hre : ∀ w, (D w).re = 0 := by
    intro w
    have h1 := (hD w).mul (hD w).star
    have hconst : ((fun t : ℝ => χ (t * w)) * fun t : ℝ => star (χ (t * w))) = fun _ => (1 : ℂ) := by
      funext t
      simp only [Pi.mul_apply]
      rw [← starRingEnd_apply, RCLike.mul_conj, hnorm]
      simp
    rw [hconst] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
    rw [hf0] at h2
    simp only [star_one, mul_one, one_mul] at h2
    have h3 := congrArg Complex.re h2
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h3
    linarith
  have hadd : ∀ z w, D (z + w) = D z + D w := by
    intro z w
    have h1 := (hD z).mul (hD w)
    have hfun : ((fun t : ℝ => χ (t * z)) * fun t : ℝ => χ (t * w)) = fun t : ℝ => χ (t * (z + w)) := by
      funext t
      simp only [Pi.mul_apply]
      rw [mul_add, hmul]
    rw [hfun, hf0, hf0, mul_one, one_mul] at h1
    exact (hD (z + w)).unique h1
  have hsmul : ∀ (r : ℝ) (z : ℂ), D (r * z) = r * D z := by
    intro r z
    have hr : HasDerivAt (fun t : ℝ => r * t) r 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
    have hz : HasDerivAt (fun t : ℝ => χ (t * z)) (D z) ((fun t : ℝ => r * t) 0) := by
      simp only [mul_zero]
      exact hD z
    have h1 := HasDerivAt.scomp (h := fun t : ℝ => r * t) (0 : ℝ) hz hr
    have hfun : ((fun t : ℝ => χ (t * z)) ∘ fun t : ℝ => r * t) = fun t : ℝ => χ (t * (r * z)) := by
      funext t
      simp only [Function.comp]
      congr 1
      push_cast
      ring
    rw [hfun] at h1
    rw [(hD (r * z)).unique h1, Complex.real_smul]
  have hzero : (∀ z, D z = 0) → False := by
    intro h0
    obtain ⟨z, hz⟩ := hnt
    apply hz
    have hder : ∀ s : ℝ, HasDerivAt (fun t : ℝ => χ (t * z)) 0 s := by
      intro s
      have h1 : HasDerivAt (fun t : ℝ => χ (((t - s : ℝ) : ℂ) * z)) (D z) s :=
        HasDerivAt.comp_sub_const (f := fun t : ℝ => χ (t * z)) s s (by rw [sub_self]; exact hD z)
      have h2 := h1.const_mul (χ (s * z))
      have hfun : (fun t : ℝ => χ (s * z) * χ (((t - s : ℝ) : ℂ) * z)) = fun t : ℝ => χ (t * z) := by
        funext t
        rw [← hmul]
        congr 1
        push_cast
        ring
      rw [hfun, h0, mul_zero] at h2
      exact h2
    have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt) (fun s => (hder s).deriv) 1 0
    simp only [Complex.ofReal_one, one_mul] at hc
    rw [hc, hf0]
  intro hcomb
  have ha : D β = Complex.I * D (β * Complex.I) := sub_eq_zero.mp hcomb
  have hb0 : D (β * Complex.I) = 0 := by
    apply Complex.ext
    · exact hre _
    · have h1 := congrArg Complex.re ha
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, hre] at h1
      simp only [Complex.zero_im]
      linarith
  have ha0 : D β = 0 := by rw [ha, hb0, mul_zero]
  apply hzero
  intro z
  have hz : z = ((z / β).re : ℂ) * β + ((z / β).im : ℂ) * (β * Complex.I) := by
    have e : z = (z / β) * β := by field_simp
    conv_lhs => rw [e, ← Complex.re_add_im (z / β)]
    ring
  rw [hz, hadd, hsmul, hsmul, ha0, hb0, mul_zero, mul_zero, add_zero]

end GlobalTheory.CompanionTheory.Unitary
