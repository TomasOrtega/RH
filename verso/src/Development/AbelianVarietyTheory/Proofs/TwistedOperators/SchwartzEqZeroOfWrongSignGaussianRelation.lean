import Mathlib

open SchwartzMap LineDeriv MeasureTheory ComplexConjugate

noncomputable section

namespace GlobalTheory.WrongSignGauss

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def sesq : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ).flip.comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)).flip

/- English proof (translation)
Simplify using `[sesq]`. Expand and normalize the polynomial expressions, which then agree.
-/
@[simp] theorem sesq_apply (u w : ℂ) : sesq u w = u * conj w := by
  simp [sesq]; ring

def mulForm (ℓ : V →ₗ[ℝ] ℝ) : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (⇑(LinearMap.toContinuousLinearMap ℓ))

/- English proof (translation)
Rewrite using `[mulForm, SchwartzMap.smulLeftCLM_apply_apply (ContinuousLinearMap.hasTemperateGrowth _)]`. Simplify using `[Complex.real_smul]`.
-/
theorem mulForm_apply (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    mulForm ℓ f x = (ℓ x : ℂ) * f x := by
  rw [mulForm, SchwartzMap.smulLeftCLM_apply_apply (ContinuousLinearMap.hasTemperateGrowth _)]
  simp [Complex.real_smul]

/- English proof (translation)
Establish `e : (⇑(mulForm ℓ f)) = ⇑(LinearMap.toContinuousLinearMap ℓ) • ⇑f`. Use function extensionality and compare the values at `y`. Rewrite using `[Pi.smul_apply', mulForm_apply, Complex.real_smul]`. Both sides reduce to the same expression. Establish `h2` using `((LinearMap.toContinuousLinearMap ℓ).hasFDerivAt (x := x)).smul (f.hasFDerivAt x)`.

Rewrite using `[SchwartzMap.lineDerivOp_apply_eq_fderiv, e, h2.fderiv]`. Simplify using `[SchwartzMap.lineDerivOp_apply_eq_fderiv, Complex.real_smul]`.
-/
theorem lineDerivOp_mulForm (v : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (mulForm ℓ f) x = (ℓ x : ℂ) * ∂_{v} f x + (ℓ v : ℂ) * f x := by
  have e : (⇑(mulForm ℓ f)) = ⇑(LinearMap.toContinuousLinearMap ℓ) • ⇑f := by
    funext y; rw [Pi.smul_apply', mulForm_apply, Complex.real_smul]; rfl
  have h2 := ((LinearMap.toContinuousLinearMap ℓ).hasFDerivAt (x := x)).smul (f.hasFDerivAt x)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, e, h2.fderiv]
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, Complex.real_smul]

/- English proof (translation)
Establish `key : ∀ (u v : V) x, ∂_{v} (∂_{u} f) x = fderiv ℝ (fderiv ℝ f) x v u`. Introduce `u v x`. Establish `hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x` using `((SchwartzMap.fderivCLM ℝ _ ℂ f).differentiableAt (x := x)).hasFDerivAt`. Establish `h1` using `((ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt (x := fderiv ℝ f x)).comp x hd`. Rewrite using `[SchwartzMap.lineDerivOp_apply_eq_fderiv]`.

Establish `e : (⇑(∂_{u} f : 𝓢(V, ℂ))) = (ContinuousLinearMap.apply ℝ ℂ u) ∘ fderiv ℝ f`. Use function extensionality and compare the values at `y`. Both sides reduce to the same expression. Rewrite using `[e, h1.fderiv]`. Both sides reduce to the same expression.

Rewrite using `[key, key]`. Conclude with `((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)) _ _`.
-/
theorem lineDerivOp_comm' (u v : V) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (∂_{u} f) x = ∂_{u} (∂_{v} f) x := by
  have key : ∀ (u v : V) x, ∂_{v} (∂_{u} f) x = fderiv ℝ (fderiv ℝ f) x v u := by
    intro u v x
    have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
      ((SchwartzMap.fderivCLM ℝ _ ℂ f).differentiableAt (x := x)).hasFDerivAt
    have h1 := ((ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt (x := fderiv ℝ f x)).comp x hd
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have e : (⇑(∂_{u} f : 𝓢(V, ℂ))) = (ContinuousLinearMap.apply ℝ ℂ u) ∘ fderiv ℝ f := by
      funext y; rfl
    rw [e, h1.fderiv]
    rfl
  rw [key, key]
  exact ((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)) _ _

def twD (a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{a} f - (2 * Real.pi * Complex.I) • mulForm ℓ f

/- English proof (translation)
Simplify using `[twD, mulForm_apply]`.
-/
theorem twD_apply (a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    twD a ℓ f x = ∂_{a} f x - 2 * Real.pi * Complex.I * ((ℓ x : ℂ) * f x) := by
  simp [twD, mulForm_apply]

section integrals

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

def ip (u w : 𝓢(V, ℂ)) : ℂ := ∫ x, u x * conj (w x) ∂μ

/- English proof (translation)
Establish `h` using `(pairing sesq u w).integrable (μ := μ)`. Simplify `h` using `[pairing_apply]`.
-/
theorem integrable_ip (u w : 𝓢(V, ℂ)) : Integrable (fun x => u x * conj (w x)) μ := by
  have h := (pairing sesq u w).integrable (μ := μ)
  simpa [pairing_apply] using h

/- English proof (translation)
Simplify using `only [ip, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]`. Conclude with `integral_const_mul c _`.
-/
theorem ip_smul_left (c : ℂ) (u w : 𝓢(V, ℂ)) : ip μ (c • u) w = c * ip μ u w := by
  simp only [ip, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

/- English proof (translation)
Simplify using `only [ip, SchwartzMap.smul_apply, smul_eq_mul, map_mul]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ip_smul_right (c : ℂ) (u w : 𝓢(V, ℂ)) : ip μ u (c • w) = conj c * ip μ u w := by
  simp only [ip, SchwartzMap.smul_apply, smul_eq_mul, map_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

/- English proof (translation)
Simplify using `only [ip, SchwartzMap.sub_apply, sub_mul]`. Conclude with `integral_sub (integrable_ip μ u w) (integrable_ip μ v w)`.
-/
theorem ip_sub_left (u v w : 𝓢(V, ℂ)) : ip μ (u - v) w = ip μ u w - ip μ v w := by
  simp only [ip, SchwartzMap.sub_apply, sub_mul]
  exact integral_sub (integrable_ip μ u w) (integrable_ip μ v w)

/- English proof (translation)
Simplify using `only [ip, SchwartzMap.sub_apply, map_sub, mul_sub]`. Conclude with `integral_sub (integrable_ip μ w u) (integrable_ip μ w v)`.
-/
theorem ip_sub_right (u v w : 𝓢(V, ℂ)) : ip μ w (u - v) = ip μ w u - ip μ w v := by
  simp only [ip, SchwartzMap.sub_apply, map_sub, mul_sub]
  exact integral_sub (integrable_ip μ w u) (integrable_ip μ w v)

/- English proof (translation)
Establish `h` using `integral_bilinear_lineDerivOp_right_eq_neg_left (μ := μ) u w sesq a`. Simplify using `only [sesq_apply] at h`. Simplify using `only [ip, h, neg_neg]`.
-/
theorem ip_lineDerivOp (a : V) (u w : 𝓢(V, ℂ)) : ip μ (∂_{a} u) w = - ip μ u (∂_{a} w) := by
  have h := integral_bilinear_lineDerivOp_right_eq_neg_left (μ := μ) u w sesq a
  simp only [sesq_apply] at h
  simp only [ip, h, neg_neg]

/- English proof (translation)
Simplify using `only [ip, mulForm_apply, map_mul, Complex.conj_ofReal]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ip_mulForm (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) : ip μ (mulForm ℓ u) w = ip μ u (mulForm ℓ w) := by
  simp only [ip, mulForm_apply, map_mul, Complex.conj_ofReal]
  congr 1; funext x; ring

/- English proof (translation)
Simplify using `only [twD, ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right, ip_lineDerivOp, ip_mulForm]`. Simplify using `[map_mul, Complex.conj_ofReal, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ip_twD (a : V) (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) :
    ip μ (twD a ℓ u) w = - ip μ u (twD a ℓ w) := by
  simp only [twD, ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right, ip_lineDerivOp, ip_mulForm]
  simp [map_mul, Complex.conj_ofReal, map_ofNat]
  ring

end integrals

/- English proof (translation)
Rewrite using `[twD, ← LineDeriv.lineDerivOpCLM_apply (R := ℂ), map_sub, map_smul, LineDeriv.lineDerivOpCLM_apply, LineDeriv.lineDerivOpCLM_apply]`. Simplify using `only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, lineDerivOp_mulForm]`.
-/
theorem lineDerivOp_twD (v a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (twD a ℓ f) x = ∂_{v} (∂_{a} f) x -
      2 * Real.pi * Complex.I * ((ℓ x : ℂ) * ∂_{v} f x + (ℓ v : ℂ) * f x) := by
  rw [twD, ← LineDeriv.lineDerivOpCLM_apply (R := ℂ), map_sub, map_smul,
    LineDeriv.lineDerivOpCLM_apply, LineDeriv.lineDerivOpCLM_apply]
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, lineDerivOp_mulForm]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, twD_apply _ _ (twD _ _ f), lineDerivOp_twD]`. Rewrite using `[twD_apply, twD_apply, lineDerivOp_comm' a₁ a₂ f x]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem twD_comm (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    twD a₁ ℓ₁ (twD a₂ ℓ₂ f) - twD a₂ ℓ₂ (twD a₁ ℓ₁ f) =
      (-(2 * Real.pi * Complex.I) * ((ℓ₂ a₁ - ℓ₁ a₂ : ℝ) : ℂ)) • f := by
  ext x
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, twD_apply _ _ (twD _ _ f),
    lineDerivOp_twD]
  rw [twD_apply, twD_apply, lineDerivOp_comm' a₁ a₂ f x]
  push_cast
  ring

section main

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

/- English proof (translation)
Rewrite using `[ip]`. Use `first`. Consider the case `rw [← integral_complex_ofReal]`. Consider the case `rw [← integral_ofReal (𝕜 := ℂ)]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`.
-/
theorem ip_self (h : 𝓢(V, ℂ)) : ip μ h h = ((∫ x, ‖h x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [ip]
  first
  | rw [← integral_complex_ofReal]
  | rw [← integral_ofReal (𝕜 := ℂ)]
  congr 1; funext x
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Establish `h1 : ip μ (twD a₁ ℓ₁ (twD a₂ ℓ₂ f)) f = -(Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f))`. Rewrite using `[ip_twD, hD, ip_smul_left]`. Establish `h2 : ip μ (twD a₂ ℓ₂ (twD a₁ ℓ₁ f)) f = -(conj Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f))`. Rewrite using `[ip_twD, hD, ip_smul_right]`. Establish `h3` using `congrArg (fun u => ip μ u f) (twD_comm a₁ a₂ ℓ₁ ℓ₂ f)`.

Simplify using `only [ip_sub_left, ip_smul_left, h1, h2, Complex.conj_I, ip_self] at h3`. Establish `E : ((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) = ((Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ)`. Move the coercions through the operations in `at h3 ⊢`. Take the linear combination `(Complex.I / 2) * h3 + (((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) - Real.pi * ((ℓ₂ a₁ : ℂ) - ℓ₁ a₂) * ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ)) * Complex.I_sq`. Conclude with `E` after adjusting the coercions.
-/
theorem norm_sq_twD (f : 𝓢(V, ℂ)) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ)
    (hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f) :
    ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ = Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h1 : ip μ (twD a₁ ℓ₁ (twD a₂ ℓ₂ f)) f = -(Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f)) := by
    rw [ip_twD, hD, ip_smul_left]
  have h2 : ip μ (twD a₂ ℓ₂ (twD a₁ ℓ₁ f)) f = -(conj Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f)) := by
    rw [ip_twD, hD, ip_smul_right]
  have h3 := congrArg (fun u => ip μ u f) (twD_comm a₁ a₂ ℓ₁ ℓ₂ f)
  simp only [ip_sub_left, ip_smul_left, h1, h2, Complex.conj_I, ip_self] at h3
  have E : ((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) =
      ((Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    push_cast at h3 ⊢
    linear_combination (Complex.I / 2) * h3 +
      (((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) - Real.pi * ((ℓ₂ a₁ : ℂ) - ℓ₁ a₂) *
        ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ)) * Complex.I_sq
  exact_mod_cast E

end main

/- English proof (translation)
Introduce `V _ _ _ f a₁ a₂ ℓ₁ ℓ₂ hf hc`. Use `letI : MeasurableSpace V := borel V`. Use `haveI : BorelSpace V := ⟨rfl⟩`. Set `μ : Measure V` to `Measure.addHaar`. Establish `hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f`.

Use extensionality with `y`. Simplify using `only [SchwartzMap.smul_apply, smul_eq_mul, twD_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]`. Take the linear combination `hf y`. Establish `hk` using `norm_sq_twD μ f a₁ a₂ ℓ₁ ℓ₂ hD`. Establish `hG : 0 ≤ ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ` using `integral_nonneg (fun x => by positivity)`.

Establish `hF : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ` using `integral_nonneg (fun x => by positivity)`. Establish `hP : Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) < 0` using `mul_neg_of_pos_of_neg Real.pi_pos hc`. Establish `hF0 : ∫ x, ‖f x‖ ^ 2 ∂μ = 0` using `by nlinarith`. Establish `hint : Integrable (fun x => ‖f x‖ ^ 2) μ`. Use `(integrable_ip μ f f).norm.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Simplify using `[norm_mul, sq]`. Rewrite `hF0` using `[integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint]`. Establish `hcont : Continuous (fun x => ‖f x‖ ^ 2)` using `f.continuous.norm.pow 2`. Establish `h0` using `(Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 hF0`. Use extensionality with `x`.

Establish `hx` using `congrFun h0 x`. Simplify using `using hx`.
-/
theorem vanish : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ),
    (∀ y, fderiv ℝ f y a₂ + (-(2 * Real.pi * Complex.I) * (ℓ₂ y : ℂ)) * f y =
      Complex.I * (fderiv ℝ f y a₁ + (-(2 * Real.pi * Complex.I) * (ℓ₁ y : ℂ)) * f y)) →
    ℓ₂ a₁ - ℓ₁ a₂ < 0 → f = 0 := by
  intro V _ _ _ f a₁ a₂ ℓ₁ ℓ₂ hf hc
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  let μ : Measure V := Measure.addHaar
  have hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f := by
    ext y
    simp only [SchwartzMap.smul_apply, smul_eq_mul, twD_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    linear_combination hf y
  have hk := norm_sq_twD μ f a₁ a₂ ℓ₁ ℓ₂ hD
  have hG : 0 ≤ ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ := integral_nonneg (fun x => by positivity)
  have hF : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg (fun x => by positivity)
  have hP : Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) < 0 := mul_neg_of_pos_of_neg Real.pi_pos hc
  have hF0 : ∫ x, ‖f x‖ ^ 2 ∂μ = 0 := by nlinarith
  have hint : Integrable (fun x => ‖f x‖ ^ 2) μ := by
    refine (integrable_ip μ f f).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_mul, sq]
  rw [integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint] at hF0
  have hcont : Continuous (fun x => ‖f x‖ ^ 2) := f.continuous.norm.pow 2
  have h0 := (Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 hF0
  ext x
  have hx := congrFun h0 x
  simpa using hx

end GlobalTheory.WrongSignGauss
