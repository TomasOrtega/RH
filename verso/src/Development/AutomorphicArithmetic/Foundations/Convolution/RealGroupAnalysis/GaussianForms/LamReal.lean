import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

/- English proof (translation)
The claim follows from `|(a ^ (1 / 2 : ℂ)).im| < (a ^ (1 / 2 : ℂ)).re := by have ha0 : a ≠ 0 := by rintro rfl simp at ha have h2 : (a ^ (1 / 2 : ℂ)) ^ 2 = a := by have := Complex.cpow_nat_inv_pow a (n := 2) two_ne_zero simpa [one_div] using this have hpos : 0 < (a ^ (1 / 2 : ℂ)).re := by have harg : |a. …`.
-/
private lemma half_root (a : ℂ) (ha : 0 < a.re) :
    (a ^ (1 / 2 : ℂ)) ^ 2 = a ∧ 0 < (a ^ (1 / 2 : ℂ)).re ∧
      |(a ^ (1 / 2 : ℂ)).im| < (a ^ (1 / 2 : ℂ)).re := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have h2 : (a ^ (1 / 2 : ℂ)) ^ 2 = a := by
    have := Complex.cpow_nat_inv_pow a (n := 2) two_ne_zero
    simpa [one_div] using this
  have hpos : 0 < (a ^ (1 / 2 : ℂ)).re := by
    have harg : |a.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl ha)
    have harg' := abs_lt.1 harg
    rw [Complex.cpow_def_of_ne_zero ha0, Complex.exp_re]
    have him : (Complex.log a * (1 / 2 : ℂ)).im = a.arg / 2 := by
      simp [Complex.log_im]
      ring
    rw [him]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;> linarith [Real.pi_pos]
  refine ⟨h2, hpos, ?_⟩
  generalize a ^ (1 / 2 : ℂ) = w at h2 hpos
  have hre : a.re = w.re ^ 2 - w.im ^ 2 := by
    rw [← h2, pow_two, Complex.mul_re]
    ring
  apply abs_lt_of_sq_lt_sq _ hpos.le
  linarith

/- English proof (translation)
Establish `hr : 0 < √|β|` using `Real.sqrt_pos.2 (abs_pos.2 hβ)`. Establish `hrc : ((√|β| : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hr.ne'`. Establish `hbc : (β : ℂ) ≠ 0` using `by exact_mod_cast hβ`. Establish `hsq : ((√|β| : ℝ) : ℂ) ^ 2 = ((|β| : ℝ) : ℂ)`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (abs_nonneg β)]`.

Establish `hI : Complex.I ^ 2 = -1` using `Complex.I_sq`. Break down `lt_or_gt_of_ne hβ with h | h` into its components or cases. Establish `hs : ((SignType.sign β : SignType) : ℂ) = -1` using `by simp [sign_neg h]`. Establish `hab : ((|β| : ℝ) : ℂ) = -(β : ℂ)`. Rewrite using `[abs_of_neg h]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Simplify using `only [lamR, hs]`. Use `push_cast`.

Rewrite using `[div_pow, mul_pow, hsq, hab]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(2 + Complex.I)) * hI`. Simplify using `only [lamR, hs]`. Rewrite using `[Complex.div_ofReal_re]`.

Simplify using the standard rewrite rules. Check the signs of the components of the expression. Establish `hs : ((SignType.sign β : SignType) : ℂ) = 1` using `by simp [sign_pos h]`. Establish `hab : ((|β| : ℝ) : ℂ) = (β : ℂ)`. Rewrite using `[abs_of_pos h]`.

Prove the components needed by the constructor for the conclusion. Simplify using `only [lamR, hs]`. Use `push_cast`. Rewrite using `[div_pow, mul_pow, hsq, hab]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `(Complex.I - 2) * hI`. Simplify using `only [lamR, hs]`. Rewrite using `[Complex.div_ofReal_re]`. Simplify using the standard rewrite rules. Check the signs of the components of the expression.
-/
private lemma lamR_props (β : ℝ) (hβ : β ≠ 0) :
    lamR β ^ 2 = 1 / (2 * Complex.I * (β : ℂ)) ∧ 0 < (lamR β).re := by
  have hr : 0 < √|β| := Real.sqrt_pos.2 (abs_pos.2 hβ)
  have hrc : ((√|β| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hbc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hsq : ((√|β| : ℝ) : ℂ) ^ 2 = ((|β| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (abs_nonneg β)]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rcases lt_or_gt_of_ne hβ with h | h
  · have hs : ((SignType.sign β : SignType) : ℂ) = -1 := by simp [sign_neg h]
    have hab : ((|β| : ℝ) : ℂ) = -(β : ℂ) := by
      rw [abs_of_neg h]; push_cast; ring
    constructor
    · simp only [lamR, hs]
      push_cast
      rw [div_pow, mul_pow, hsq, hab]
      field_simp
      linear_combination (-(2 + Complex.I)) * hI
    · simp only [lamR, hs]
      rw [Complex.div_ofReal_re]
      simp
      positivity
  · have hs : ((SignType.sign β : SignType) : ℂ) = 1 := by simp [sign_pos h]
    have hab : ((|β| : ℝ) : ℂ) = (β : ℂ) := by
      rw [abs_of_pos h]
    constructor
    · simp only [lamR, hs]
      push_cast
      rw [div_pow, mul_pow, hsq, hab]
      field_simp
      linear_combination (Complex.I - 2) * hI
    · simp only [lamR, hs]
      rw [Complex.div_ofReal_re]
      simp
      positivity

/- English proof (translation)
Introduce `β hβ`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `hbc : (β : ℂ) ≠ 0` using `by exact_mod_cast hβ`. Establish `hI0 : Complex.I ≠ 0` using `Complex.I_ne_zero`. Take `⟨D, hDdef⟩ : ∃ D : ℂ, D = 1 + 2 * Complex.I * (β : ℂ)` from `⟨_, rfl⟩`.

Establish `hDre : D.re = 1` using `by simp [hDdef]`. Establish `hDim : D.im = 2 * β` using `by simp [hDdef]`. Establish `hD : D ≠ 0`. Introduce `h`. Rewrite `hDre` using `[h]`.

Simplify using `at hDre`. Establish `hnsq : 0 < Complex.normSq D` using `Complex.normSq_pos.2 hD`. Take `⟨s, hsdef⟩ : ∃ s : ℂ, s = 2 * Complex.I * (β : ℂ) / D` from `⟨_, rfl⟩`. Establish `hs0 : s ≠ 0`. Rewrite using `[hsdef]`.

Conclude with `div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hI0) hbc) hD`. Establish `hsre : 0 < s.re`. Rewrite using `[hsdef, Complex.div_re]`. Establish `e1 : (2 * Complex.I * (β : ℂ)).re = 0` using `by simp`. Establish `e2 : (2 * Complex.I * (β : ℂ)).im = 2 * β` using `by simp`.

Rewrite using `[e1, e2, hDim, zero_mul, zero_div, zero_add]`. Establish `: 0 < 2 * β * (2 * β)`. Use `mul_self_pos.2 (mul_ne_zero two_ne_zero hβ)` as an intermediate fact. Simplify using `using this`. Conclude with `div_pos this hnsq`.

Establish `hinvD : 0 < (1 / D).re`. Rewrite using `[one_div, Complex.inv_re, hDre]`. Conclude with `div_pos one_pos hnsq`. Establish `hinvs : 0 < (1 / s).re`. Rewrite using `[one_div, Complex.inv_re]`.

Conclude with `div_pos hsre (Complex.normSq_pos.2 hs0)`. Establish `hb : (-(Real.pi : ℂ) * D).re < 0`. Simplify using `[hDre, hDim, Real.pi_pos]`. Establish `hinner : ∀ y : ℝ, (∫ x : ℝ, Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) * Complex.exp (-(2 * Real.pi * Complex.I) * (β : ℂ) * ((x + y : ℝ) : ℂ) ^ 2)) = (1 / D) ^ (1 / 2 : ℂ) * Complex.exp (-((Real.pi : ℂ) * s) * (y : ℂ) ^ 2)`. Introduce `y`.

Establish `hfun : (fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) * Complex.exp (-(2 * Real.pi * Complex.I) * (β : ℂ) * ((x + y : ℝ) : ℂ) ^ 2)) = fun x : ℝ => Complex.exp ((-(Real.pi : ℂ) * D) * (x : ℂ) ^ 2 + (-(4 * Real.pi * Complex.I * (β : ℂ) * (y : ℂ))) * (x : ℂ) + (-(2 * Real. …`. Use function extensionality and compare the values at `x`. Rewrite using `[← Complex.exp_add, hDdef]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun, integral_cexp_quadratic hb]`. Use `congr 1`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Use `congr 1`. Rewrite using `[hsdef, hDdef]`. Establish `hD' : (1 + 2 * Complex.I * (β : ℂ)) ≠ 0` using `hDdef ▸ hD`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Unfold `abelian₂`. Simplify using `only [hinner]`. Rewrite using `[integral_const_mul]`. Establish `houter : (∫ y : ℝ, Complex.exp (-((Real.pi : ℂ) * s) * (y : ℂ) ^ 2)) = (1 / s) ^ (1 / 2 : ℂ)`. Establish `hre : 0 < ((Real.pi : ℂ) * s).re`.

Simplify using `using mul_pos Real.pi_pos hsre`. Rewrite using `[integral_gaussian_complex hre]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[houter]`.

Take `⟨hA2, hApos, hAim⟩` from `half_root _ hinvD`. Take `⟨hB2, hBpos, hBim⟩` from `half_root _ hinvs`. Take `⟨hL2, hLpos⟩` from `lamR_props β hβ`. Generalize the expression as in `(1 / D) ^ (1 / 2 : ℂ) = A at hA2 hApos hAim`. Generalize the expression as in `(1 / s) ^ (1 / 2 : ℂ) = B at hB2 hBpos hBim`.

Establish `hsq : (A * B) ^ 2 = lamR β ^ 2`. Rewrite using `[mul_pow, hA2, hB2, hL2, hsdef]`. Clear the denominators using the available nonvanishing facts. Establish `hzre : 0 < (A * B).re`. Rewrite using `[Complex.mul_re]`.

Establish `h1 : A.im * B.im ≤ |A.im| * |B.im|`. Rewrite using `[← abs_mul]`. Conclude with `le_abs_self _`. Establish `h2 : |A.im| * |B.im| < A.re * B.re` using `mul_lt_mul'' hAim hBim (abs_nonneg _) (abs_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion.

Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Rewrite `hzre` using `[h, Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.lamReal :
    ∀ β : ℝ, β ≠ 0 → abelian₂ (volume : Measure ℝ) (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * (β : ℂ) * (x : ℂ) ^ 2)) (fun x => Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)) = lamR β := by
  intro β hβ
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hbc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  obtain ⟨D, hDdef⟩ : ∃ D : ℂ, D = 1 + 2 * Complex.I * (β : ℂ) := ⟨_, rfl⟩
  have hDre : D.re = 1 := by simp [hDdef]
  have hDim : D.im = 2 * β := by simp [hDdef]
  have hD : D ≠ 0 := by
    intro h
    rw [h] at hDre
    simp at hDre
  have hnsq : 0 < Complex.normSq D := Complex.normSq_pos.2 hD
  obtain ⟨s, hsdef⟩ : ∃ s : ℂ, s = 2 * Complex.I * (β : ℂ) / D := ⟨_, rfl⟩
  have hs0 : s ≠ 0 := by
    rw [hsdef]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hI0) hbc) hD
  have hsre : 0 < s.re := by
    rw [hsdef, Complex.div_re]
    have e1 : (2 * Complex.I * (β : ℂ)).re = 0 := by simp
    have e2 : (2 * Complex.I * (β : ℂ)).im = 2 * β := by simp
    rw [e1, e2, hDim, zero_mul, zero_div, zero_add]
    have : 0 < 2 * β * (2 * β) := by
      have := mul_self_pos.2 (mul_ne_zero two_ne_zero hβ)
      simpa using this
    exact div_pos this hnsq
  have hinvD : 0 < (1 / D).re := by
    rw [one_div, Complex.inv_re, hDre]
    exact div_pos one_pos hnsq
  have hinvs : 0 < (1 / s).re := by
    rw [one_div, Complex.inv_re]
    exact div_pos hsre (Complex.normSq_pos.2 hs0)
  have hb : (-(Real.pi : ℂ) * D).re < 0 := by
    simp [hDre, hDim, Real.pi_pos]
  have hinner : ∀ y : ℝ,
      (∫ x : ℝ, Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (β : ℂ) * ((x + y : ℝ) : ℂ) ^ 2)) =
      (1 / D) ^ (1 / 2 : ℂ) * Complex.exp (-((Real.pi : ℂ) * s) * (y : ℂ) ^ 2) := by
    intro y
    have hfun : (fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (β : ℂ) * ((x + y : ℝ) : ℂ) ^ 2)) =
        fun x : ℝ => Complex.exp ((-(Real.pi : ℂ) * D) * (x : ℂ) ^ 2 +
          (-(4 * Real.pi * Complex.I * (β : ℂ) * (y : ℂ))) * (x : ℂ) +
          (-(2 * Real.pi * Complex.I) * (β : ℂ) * (y : ℂ) ^ 2)) := by
      funext x
      rw [← Complex.exp_add, hDdef]
      congr 1
      push_cast
      ring
    rw [hfun, integral_cexp_quadratic hb]
    congr 1
    · congr 1
      field_simp
    · congr 1
      rw [hsdef, hDdef]
      have hD' : (1 + 2 * Complex.I * (β : ℂ)) ≠ 0 := hDdef ▸ hD
      field_simp
      ring
  unfold abelian₂
  simp only [hinner]
  rw [integral_const_mul]
  have houter : (∫ y : ℝ, Complex.exp (-((Real.pi : ℂ) * s) * (y : ℂ) ^ 2)) = (1 / s) ^ (1 / 2 : ℂ) := by
    have hre : 0 < ((Real.pi : ℂ) * s).re := by
      simpa using mul_pos Real.pi_pos hsre
    rw [integral_gaussian_complex hre]
    congr 1
    field_simp
  rw [houter]
  obtain ⟨hA2, hApos, hAim⟩ := half_root _ hinvD
  obtain ⟨hB2, hBpos, hBim⟩ := half_root _ hinvs
  obtain ⟨hL2, hLpos⟩ := lamR_props β hβ
  generalize (1 / D) ^ (1 / 2 : ℂ) = A at hA2 hApos hAim
  generalize (1 / s) ^ (1 / 2 : ℂ) = B at hB2 hBpos hBim
  have hsq : (A * B) ^ 2 = lamR β ^ 2 := by
    rw [mul_pow, hA2, hB2, hL2, hsdef]
    field_simp
  have hzre : 0 < (A * B).re := by
    rw [Complex.mul_re]
    have h1 : A.im * B.im ≤ |A.im| * |B.im| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h2 : |A.im| * |B.im| < A.re * B.re :=
      mul_lt_mul'' hAim hBim (abs_nonneg _) (abs_nonneg _)
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact h
  · exfalso
    rw [h, Complex.neg_re] at hzre
    linarith
