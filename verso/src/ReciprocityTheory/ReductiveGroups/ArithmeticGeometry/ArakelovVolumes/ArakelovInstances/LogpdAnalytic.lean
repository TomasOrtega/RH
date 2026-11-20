import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.DiagonalCurvatureCoefficient

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology

variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)

/- English proof (translation)
Unfold `fn`. Simplify using `only [Pi.zero_apply]`. Establish `h : Gnz hm D Y 0 = Matrix.diagonal fun a : Fin m => ((D (Fin.castLE hm a) : ℝ) : ℂ)`. Simplify using `only [Gnz, Gz, zero_smul, sub_zero, add_zero, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Use `first`.

Consider the case `exact Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)`. Consider the case `simp [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)]`. Consider the case `(ext i j`. Simplify using `[Matrix.diagonal_apply, (Fin.castLE_injective hm).eq_iff])`. Rewrite using `[h, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun a _ => hD _`.
-/
theorem fn_zero_ne (hD : ∀ k, D k ≠ 0) : fn hm D Y 0 ≠ 0 := by
  unfold fn
  simp only [Pi.zero_apply]
  have h : Gnz hm D Y 0 = Matrix.diagonal fun a : Fin m => ((D (Fin.castLE hm a) : ℝ) : ℂ) := by
    simp only [Gnz, Gz, zero_smul, sub_zero, add_zero, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
    first
    | exact Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)
    | simp [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)]
    | (ext i j
       simp [Matrix.diagonal_apply, (Fin.castLE_injective hm).eq_iff])
  rw [h, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Finset.prod_ne_zero_iff.2 fun a _ => hD _

/- English proof (translation)
Establish `hc : ContDiffAt ℝ 2 (fn hm D Y) 0` using `(contDiff_fn hm D Y).contDiffAt`. Establish `h0` using `fn_zero_ne hm D Y hD`. Establish `h` using `leviHalfLogAbs (ι := Fin 1) (fn hm D Y) 0 hc h0 (fderiv_fn_zero hm D Y) (fun _ => 1)`. Establish `hL : ContDiffAt ℝ 2 (fun x => (1 / 2 : ℝ) * Real.log |fn hm D Y x|) 0`. Establish `e : (fun x => (1 / 2 : ℝ) * Real.log |fn hm D Y x|) = fun x => (1 / 2 : ℝ) * Real.log (fn hm D Y x)`.

Use function extensionality and compare the values at `x`. Rewrite using `[Real.log_abs]`. Rewrite using `[e]`. Conclude with `contDiffAt_const.mul (hc.log h0)`. Establish `e : (fun v => Real.log |fn hm D Y v|) = fun v => (1 / 2 * Real.log |fn hm D Y v|) + 1 * (1 / 2 * Real.log |fn hm D Y v|)`.

Use function extensionality and compare the values at `v`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, levi_add_smul 1 hL hL, h]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem levi_logfn (hD : ∀ k, D k ≠ 0) :
    levi (fun v => Real.log |fn hm D Y v|) 0 (fun _ => 1) =
      levi (fn hm D Y) 0 (fun _ => 1) / fn hm D Y 0 := by
  have hc : ContDiffAt ℝ 2 (fn hm D Y) 0 := (contDiff_fn hm D Y).contDiffAt
  have h0 := fn_zero_ne hm D Y hD
  have h := leviHalfLogAbs (ι := Fin 1) (fn hm D Y) 0 hc h0 (fderiv_fn_zero hm D Y) (fun _ => 1)
  have hL : ContDiffAt ℝ 2 (fun x => (1 / 2 : ℝ) * Real.log |fn hm D Y x|) 0 := by
    have e : (fun x => (1 / 2 : ℝ) * Real.log |fn hm D Y x|) = fun x => (1 / 2 : ℝ) * Real.log (fn hm D Y x) := by
      funext x; rw [Real.log_abs]
    rw [e]
    exact contDiffAt_const.mul (hc.log h0)
  have e : (fun v => Real.log |fn hm D Y v|) =
      fun v => (1 / 2 * Real.log |fn hm D Y v|) + 1 * (1 / 2 * Real.log |fn hm D Y v|) := by
    funext v; ring
  rw [e, levi_add_smul 1 hL hL, h]
  field_simp
  ring

/- English proof (translation)
Establish `hD : (Matrix.diagonal fun k => (D k : ℂ))ᴴ = Matrix.diagonal fun k => (D k : ℂ)`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Use `first`. Consider the case `simp only [Gz, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]`. Consider the case `(unfold Gz`. Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Use `erw [hD]`.

Simplify using `only [Matrix.mul_assoc])`.
-/
theorem Gz_herm (ζ : ℂ) : (Gz hm D Y ζ)ᴴ = Gz hm D Y ζ := by
  have hD : (Matrix.diagonal fun k => (D k : ℂ))ᴴ = Matrix.diagonal fun k => (D k : ℂ) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext k
    simp
  first
  | simp only [Gz, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
  | (unfold Gz
     rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
       Matrix.conjTranspose_conjTranspose]
     erw [hD]
     simp only [Matrix.mul_assoc])

/- English proof (translation)
Establish `key : ∀ (p G : ℂ), (star p * (G * p)).re = ‖p‖ ^ 2 * G.re`. Introduce `p G`. Establish `h1 : star p * (G * p) = ((Complex.normSq p : ℝ) : ℂ) * G`. Rewrite using `[Complex.star_def, ← Complex.mul_conj]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, Complex.re_ofReal_mul]`. Use `first`. Consider the case `rw [Complex.normSq_eq_norm_sq]`. Consider the case `rw [← Complex.sq_norm]`. Consider the case `simp [Complex.normSq_eq_norm_sq]`.

Simplify using `only [fn, fY, Gnz, pd, Matrix.det_mul, Matrix.det_conjTranspose]`. Conclude with `key _ _`.
-/
theorem fn_eq (v : Fin 1 → ℂ) : fn hm D Y v = ‖pd hm Y v‖ ^ 2 * fY hm D Y v := by
  have key : ∀ (p G : ℂ), (star p * (G * p)).re = ‖p‖ ^ 2 * G.re := by
    intro p G
    have h1 : star p * (G * p) = ((Complex.normSq p : ℝ) : ℂ) * G := by
      rw [Complex.star_def, ← Complex.mul_conj]
      ring
    rw [h1, Complex.re_ofReal_mul]
    first
    | rw [Complex.normSq_eq_norm_sq]
    | rw [← Complex.sq_norm]
    | simp [Complex.normSq_eq_norm_sq]
  simp only [fn, fY, Gnz, pd, Matrix.det_mul, Matrix.det_conjTranspose]
  exact key _ _

/- English proof (translation)
Unfold `pd lin`. Rewrite using `[← Polynomial.coe_evalRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Apply the tactic sequence `simp [Matrix.one_apply, sub_eq_add_neg] <;> ring`. Apply the tactic sequence `simp [Matrix.one_apply, h, sub_eq_add_neg] <;> ring`.
-/
theorem pd_eval (v : Fin 1 → ℂ) : pd hm Y v = (lin (-(Ym hm Y))).det.eval (v 0) := by
  unfold pd lin
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply, sub_eq_add_neg] <;> ring
  · simp [Matrix.one_apply, h, sub_eq_add_neg] <;> ring

/- English proof (translation)
Establish `e : pd hm Y = (fun z => (lin (-(Ym hm Y))).det.eval z) ∘ (fun v : Fin 1 → ℂ => v 0)`. Use function extensionality and compare the values at `fun v => pd_eval hm Y v`. Rewrite using `[e]`. Conclude with `((lin (-(Ym hm Y))).det.differentiable.analyticAt _).comp ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _)`.
-/
theorem pd_analytic : AnalyticAt ℂ (pd hm Y) 0 := by
  have e : pd hm Y = (fun z => (lin (-(Ym hm Y))).det.eval z) ∘ (fun v : Fin 1 → ℂ => v 0) :=
    funext fun v => pd_eval hm Y v
  rw [e]
  exact ((lin (-(Ym hm Y))).det.differentiable.analyticAt _).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _)

/- English proof (translation)
Simplify using `[pd]`.
-/
theorem pd_zero : pd hm Y 0 = 1 := by
  simp [pd]

/- English proof (translation)
Establish `h0 : pd hm Y 0 ∈ Complex.slitPlane`. Rewrite using `[pd_zero]`. Conclude with `Complex.one_mem_slitPlane`. Conclude with `analyticAt_const.mul ((pd_analytic hm Y).clog h0)`.
-/
theorem logpd_analytic : AnalyticAt ℂ (fun v => 2 * Complex.log (pd hm Y v)) 0 := by
  have h0 : pd hm Y 0 ∈ Complex.slitPlane := by
    rw [pd_zero]
    exact Complex.one_mem_slitPlane
  exact analyticAt_const.mul ((pd_analytic hm Y).clog h0)

/- English proof (translation)
Establish `h : (2 * Complex.log (pd hm Y v)).re = 2 * (Complex.log (pd hm Y v)).re`. Simplify using `[Complex.mul_re]`. Rewrite using `[h, Complex.log_re, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logpd_eq (v : Fin 1 → ℂ) : Real.log (‖pd hm Y v‖ ^ 2) = (2 * Complex.log (pd hm Y v)).re := by
  have h : (2 * Complex.log (pd hm Y v)).re = 2 * (Complex.log (pd hm Y v)).re := by
    simp [Complex.mul_re]
  rw [h, Complex.log_re, Real.log_pow]
  push_cast
  ring

/- English proof (translation)
Establish `e : (fun v => Real.log (‖pd hm Y v‖ ^ 2)) = fun v => (2 * Complex.log (pd hm Y v)).re`. Use function extensionality and compare the values at `fun v => logpd_eq hm Y v`. Rewrite using `[e]`. Conclude with `levi_re_analytic (logpd_analytic hm Y) w`.
-/
theorem levi_logpd (w : Fin 1 → ℂ) : levi (fun v => Real.log (‖pd hm Y v‖ ^ 2)) 0 w = 0 := by
  have e : (fun v => Real.log (‖pd hm Y v‖ ^ 2)) = fun v => (2 * Complex.log (pd hm Y v)).re :=
    funext fun v => logpd_eq hm Y v
  rw [e]
  exact levi_re_analytic (logpd_analytic hm Y) w

/- English proof (translation)
Establish `hP : (∏ a : Fin m, D (Fin.castLE hm a)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun a _ => hD _`. Establish `hfY0 : fY hm D Y 0 ≠ 0` using `by rw [fY_zero]; exact hP`. Establish `h0` using `fn_zero_ne hm D Y hD`. Establish `hcont : ContinuousAt (fY hm D Y) 0` using `(contDiff_fY hm D Y).continuous.continuousAt`. Establish `hpdc : ContinuousAt (pd hm Y) 0` using `(pd_analytic hm Y).continuousAt`.

Establish `hev : (fun v => Real.log |fY hm D Y v|) =ᶠ[𝓝 0] fun v => Real.log |fn hm D Y v| + (-1) * Real.log (‖pd hm Y v‖ ^ 2)` using `by filter_upwards [hcont.eventually_ne hfY0, hpdc.eventually_ne (by rw [pd_zero]; exact one_ne_zero)] with v h1 h2`. Establish `hp : ‖pd hm Y v‖ ^ 2 ≠ 0` using `pow_ne_zero 2 (norm_ne_zero_iff.2 h2)`. Rewrite using `[Real.log_abs, Real.log_abs, fn_eq, Real.log_mul hp h1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hL1 : ContDiffAt ℝ 2 (fun v => Real.log |fn hm D Y v|) 0`.

Establish `e : (fun v => Real.log |fn hm D Y v|) = fun v => Real.log (fn hm D Y v)`. Use function extensionality and compare the values at `v`. Rewrite using `[Real.log_abs]`. Rewrite using `[e]`. Conclude with `(contDiff_fn hm D Y).contDiffAt.log h0`.

Establish `hL2 : ContDiffAt ℝ 2 (fun v => Real.log (‖pd hm Y v‖ ^ 2)) 0`. Rewrite using `[funext (logpd_eq hm Y)]`. Conclude with `Complex.reCLM.contDiff.contDiffAt.comp _ ((logpd_analytic hm Y).contDiffAt.restrict_scalars ℝ)`. Rewrite using `[levi_congr hev, levi_add_smul (-1) hL1 hL2, levi_logpd, levi_logfn hm D Y hD, levi_fn hm D Y hD, fn_zero, mul_zero, add_zero, mul_div_cancel_left₀ _ hP]`.
-/
theorem core_levi (hD : ∀ k, D k ≠ 0) :
    levi (fun v => Real.log |fY hm D Y v|) 0 (fun _ => 1) =
      ∑ a : Fin m, (D (Fin.castLE hm a))⁻¹ * Sa hm D Y a := by
  have hP : (∏ a : Fin m, D (Fin.castLE hm a)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hD _
  have hfY0 : fY hm D Y 0 ≠ 0 := by rw [fY_zero]; exact hP
  have h0 := fn_zero_ne hm D Y hD
  have hcont : ContinuousAt (fY hm D Y) 0 := (contDiff_fY hm D Y).continuous.continuousAt
  have hpdc : ContinuousAt (pd hm Y) 0 := (pd_analytic hm Y).continuousAt
  have hev : (fun v => Real.log |fY hm D Y v|) =ᶠ[𝓝 0]
      fun v => Real.log |fn hm D Y v| + (-1) * Real.log (‖pd hm Y v‖ ^ 2) := by
    filter_upwards [hcont.eventually_ne hfY0, hpdc.eventually_ne (by rw [pd_zero]; exact one_ne_zero)]
      with v h1 h2
    have hp : ‖pd hm Y v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 h2)
    rw [Real.log_abs, Real.log_abs, fn_eq, Real.log_mul hp h1]
    ring
  have hL1 : ContDiffAt ℝ 2 (fun v => Real.log |fn hm D Y v|) 0 := by
    have e : (fun v => Real.log |fn hm D Y v|) = fun v => Real.log (fn hm D Y v) := by
      funext v; rw [Real.log_abs]
    rw [e]
    exact (contDiff_fn hm D Y).contDiffAt.log h0
  have hL2 : ContDiffAt ℝ 2 (fun v => Real.log (‖pd hm Y v‖ ^ 2)) 0 := by
    rw [funext (logpd_eq hm Y)]
    exact Complex.reCLM.contDiff.contDiffAt.comp _
      ((logpd_analytic hm Y).contDiffAt.restrict_scalars ℝ)
  rw [levi_congr hev, levi_add_smul (-1) hL1 hL2, levi_logpd, levi_logfn hm D Y hD, levi_fn hm D Y hD,
    fn_zero, mul_zero, add_zero, mul_div_cancel_left₀ _ hP]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
