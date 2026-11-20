import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

def dbv {n : ℕ} (D : V n →L[ℝ] ℂ) (ζ : V n) : ℂ := (D ζ + I * D (I • ζ)) / 2

def dv {n : ℕ} (D : V n →L[ℝ] ℂ) (ζ : V n) : ℂ := (D ζ - I * D (I • ζ)) / 2

/- English proof (translation)
Use `conv_lhs => rw [← Complex.re_add_im c]`. Rewrite using `[add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_add, D.map_smul, D.map_smul, Complex.real_smul, Complex.real_smul]`.
-/
theorem clm_smul_decomp {n : ℕ} (D : V n →L[ℝ] ℂ) (c : ℂ) (e : V n) :
    D (c • e) = c.re * D e + c.im * D (I • e) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_add, D.map_smul, D.map_smul,
    Complex.real_smul, Complex.real_smul]

/- English proof (translation)
Establish `h` using `(EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr w`. Use `conv_lhs => rw [← h]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]`. Both sides reduce to the same expression.
-/
theorem vec_expand {n : ℕ} (w : V n) : w = ∑ j, w j • bas n j := by
  have h := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr w
  conv_lhs => rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  rfl

/- English proof (translation)
Use `conv_lhs => rw [vec_expand ζ]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => clm_smul_decomp D (ζ k) (bas n k)`.
-/
private theorem clm_apply_eq_sum_re_im_basis {n : ℕ} (D : V n →L[ℝ] ℂ) (ζ : V n) :
    D ζ = ∑ k, ((ζ k).re * D (bas n k) + (ζ k).im * D (I • bas n k)) := by
  conv_lhs => rw [vec_expand ζ]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => clm_smul_decomp D (ζ k) (bas n k)

/- English proof (translation)
Unfold `dbv`. Rewrite using `[clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) ζ, clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) (I • ζ), Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [wdb, PiLp.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`.
-/
theorem sum_wdb_eq {n : ℕ} (g : V n → ℂ) (y : V n) (ζ : V n) :
    ∑ k, wdb n k g y * conj (ζ k) = dbv (fderiv ℝ g y) ζ := by
  unfold dbv
  rw [clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) ζ, clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) (I • ζ), Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [wdb, PiLp.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]
  apply Complex.ext <;> simp <;> ring

/- English proof (translation)
Unfold `dv`. Rewrite using `[clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) ζ, clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) (I • ζ), Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [wd, PiLp.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`.
-/
theorem sum_wd_eq {n : ℕ} (g : V n → ℂ) (y : V n) (ζ : V n) :
    ∑ k, wd n k g y * ζ k = dv (fderiv ℝ g y) ζ := by
  unfold dv
  rw [clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) ζ, clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) (I • ζ), Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [wd, PiLp.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]
  apply Complex.ext <;> simp <;> ring

/- English proof (translation)
Establish `hI : ‖D (I • ζ)‖ ≤ ‖D‖ * ‖ζ‖`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : ‖D ζ + I * D (I • ζ)‖ ≤ ‖D‖ * ‖ζ‖ + ‖D‖ * ‖ζ‖`. Combine the equalities or inequalities in the displayed calculation. Unfold `dbv`.

Rewrite using `[norm_div, Complex.norm_two]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_dbv_le {n : ℕ} (D : V n →L[ℝ] ℂ) (ζ : V n) : ‖dbv D ζ‖ ≤ ‖D‖ * ‖ζ‖ := by
  have hI : ‖D (I • ζ)‖ ≤ ‖D‖ * ‖ζ‖ := by
    calc ‖D (I • ζ)‖ ≤ ‖D‖ * ‖I • ζ‖ := D.le_opNorm _
      _ = ‖D‖ * ‖ζ‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  have h1 : ‖D ζ + I * D (I • ζ)‖ ≤ ‖D‖ * ‖ζ‖ + ‖D‖ * ‖ζ‖ := by
    calc ‖D ζ + I * D (I • ζ)‖ ≤ ‖D ζ‖ + ‖I * D (I • ζ)‖ := norm_add_le _ _
      _ = ‖D ζ‖ + ‖D (I • ζ)‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖D‖ * ‖ζ‖ + ‖D‖ * ‖ζ‖ := add_le_add (D.le_opNorm ζ) hI
  unfold dbv
  rw [norm_div, Complex.norm_two]
  linarith

/- English proof (translation)
Establish `hF : DifferentiableAt ℝ (fderiv ℝ g) y` using `(hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hd : ∀ k, DifferentiableAt ℝ (wdb n k g) y`. Introduce `k`. Unfold `wdb`. Establish `h1 : DifferentiableAt ℝ (fun v => fderiv ℝ g v (bas n k)) y` using `hF.clm_apply (differentiableAt_const _)`.

Establish `h2 : DifferentiableAt ℝ (fun v => fderiv ℝ g v (I • bas n k)) y` using `hF.clm_apply (differentiableAt_const _)`. Establish `h3 : DifferentiableAt ℝ (fun v => fderiv ℝ g v (bas n k) + I * fderiv ℝ g v (I • bas n k)) y` using `h1.add (h2.const_mul I)`. Simplify `h3.mul_const (2⁻¹ : ℂ)` using `only [div_eq_mul_inv]`. Establish `hsum : (fun v => dbv (fderiv ℝ g v) (WithLp.toLp 2 ξ)) = fun v => ∑ k, wdb n k g v * conj (ξ k)`. Use function extensionality and compare the values at `v`.

Rewrite using `[← sum_wdb_eq]`. Establish `hD : HasFDerivAt (fun v => ∑ k, wdb n k g v * conj (ξ k)) (∑ k, conj (ξ k) • fderiv ℝ (wdb n k g) y) y` using `HasFDerivAt.fun_sum fun k _ => (hd k).hasFDerivAt.mul_const (conj (ξ k))`. Rewrite using `[hsum, ← sum_wd_eq]`. Unfold `leviV`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [wd]`. Rewrite using `[hD.fderiv]`. Simplify using `only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, WithLp.ofLp_toLp]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = _ * ξ j`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem leviV_eq_dv {n : ℕ} {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℝ 2 g y) (ξ : Fin n → ℂ) :
    leviV n g y ξ =
      dv (fderiv ℝ (fun v => dbv (fderiv ℝ g v) (WithLp.toLp 2 ξ)) y) (WithLp.toLp 2 ξ) := by
  have hF : DifferentiableAt ℝ (fderiv ℝ g) y :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd : ∀ k, DifferentiableAt ℝ (wdb n k g) y := by
    intro k
    unfold wdb
    have h1 : DifferentiableAt ℝ (fun v => fderiv ℝ g v (bas n k)) y :=
      hF.clm_apply (differentiableAt_const _)
    have h2 : DifferentiableAt ℝ (fun v => fderiv ℝ g v (I • bas n k)) y :=
      hF.clm_apply (differentiableAt_const _)
    have h3 : DifferentiableAt ℝ
        (fun v => fderiv ℝ g v (bas n k) + I * fderiv ℝ g v (I • bas n k)) y :=
      h1.add (h2.const_mul I)
    simpa only [div_eq_mul_inv] using h3.mul_const (2⁻¹ : ℂ)
  have hsum : (fun v => dbv (fderiv ℝ g v) (WithLp.toLp 2 ξ)) =
      fun v => ∑ k, wdb n k g v * conj (ξ k) := by
    funext v
    rw [← sum_wdb_eq]
  have hD : HasFDerivAt (fun v => ∑ k, wdb n k g v * conj (ξ k))
      (∑ k, conj (ξ k) • fderiv ℝ (wdb n k g) y) y :=
    HasFDerivAt.fun_sum fun k _ => (hd k).hasFDerivAt.mul_const (conj (ξ k))
  rw [hsum, ← sum_wd_eq]
  unfold leviV
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [wd]
  rw [hD.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, WithLp.ofLp_toLp]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  change _ = _ * ξ j
  ring

/- English proof (translation)
Rewrite using `[fderiv_comp v hf (hΦ.restrictScalars ℝ), hΦ.fderiv_restrictScalars ℝ]`. Simplify using `[dbv]`.
-/
theorem dbv_comp {n : ℕ} {f : V n → ℂ} {Φ : V n → V n} {v : V n}
    (hf : DifferentiableAt ℝ f (Φ v)) (hΦ : DifferentiableAt ℂ Φ v) (ζ : V n) :
    dbv (fderiv ℝ (f ∘ Φ) v) ζ = dbv (fderiv ℝ f (Φ v)) (fderiv ℂ Φ v ζ) := by
  rw [fderiv_comp v hf (hΦ.restrictScalars ℝ), hΦ.fderiv_restrictScalars ℝ]
  simp [dbv]

/- English proof (translation)
Establish `hv` using `contDiffAt_normSq_comp hG`. Establish `hpos : 0 < Complex.normSq (G x)` using `Complex.normSq_pos.2 h0`. Establish `hk : ContDiffAt ℝ 2 Real.log (Complex.normSq (G x))` using `Real.contDiffAt_log.2 hpos.ne'`. Establish `h` using `leviChain n Real.log (fun y => Complex.normSq (G y)) x ξ hv hk`. Rewrite using `[h, leviV_normSq_comp hG]`.

Simplify using `only [wd_normSq_comp hG]`. Establish `hfac : ∑ j, wd n j G x * conj (G x) * ξ j = conj (G x) * ∑ j, wd n j G x * ξ j`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[hfac, Complex.normSq_mul, Complex.normSq_conj, Real.deriv_log', deriv_inv]`.

Establish `hne : (Complex.normSq (G x) : ℂ) ≠ 0` using `by exact_mod_cast hpos.ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem leviV_log_normSq {n : ℕ} {G : V n → ℂ} {x : V n} (hG : ContDiffAt ℂ 2 G x)
    (h0 : G x ≠ 0) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((Real.log (Complex.normSq (G v)) : ℝ) : ℂ)) x ξ = 0 := by
  have hv := contDiffAt_normSq_comp hG
  have hpos : 0 < Complex.normSq (G x) := Complex.normSq_pos.2 h0
  have hk : ContDiffAt ℝ 2 Real.log (Complex.normSq (G x)) := Real.contDiffAt_log.2 hpos.ne'
  have h := leviChain n Real.log (fun y => Complex.normSq (G y)) x ξ hv hk
  rw [h, leviV_normSq_comp hG]
  simp only [wd_normSq_comp hG]
  have hfac : ∑ j, wd n j G x * conj (G x) * ξ j = conj (G x) * ∑ j, wd n j G x * ξ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfac, Complex.normSq_mul, Complex.normSq_conj, Real.deriv_log', deriv_inv]
  have hne : (Complex.normSq (G x) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast
  field_simp
  ring

/- English proof (translation)
Rewrite using `[fderiv_comp v hh (hΦ.restrictScalars ℝ), hΦ.fderiv_restrictScalars ℝ]`. Simplify using `[dv]`.
-/
private theorem dv_fderiv_comp_holomorphic {n : ℕ} {h : V n → ℂ} {Φ : V n → V n} {v : V n}
    (hh : DifferentiableAt ℝ h (Φ v)) (hΦ : DifferentiableAt ℂ Φ v) (ζ : V n) :
    dv (fderiv ℝ (h ∘ Φ) v) ζ = dv (fderiv ℝ h (Φ v)) (fderiv ℂ Φ v ζ) := by
  rw [fderiv_comp v hh (hΦ.restrictScalars ℝ), hΦ.fderiv_restrictScalars ℝ]
  simp [dv]

/- English proof (translation)
Establish `h` using `(hc.restrictScalars ℝ).hasFDerivAt.star`. Establish `hL : fderiv ℂ c y (I • ζ) = I * fderiv ℂ c y ζ` using `by rw [map_smul, smul_eq_mul]`. Establish `hfun : (fun v => conj (c v)) = fun v => star (c v)` using `rfl`. Rewrite using `[hfun, h.fderiv, hc.fderiv_restrictScalars ℝ]`. Simplify using `only [dv, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', hL]`.

Simplify using `only [ContinuousLinearEquiv.coe_coe, starL'_apply, star_mul', Complex.star_def, Complex.conj_I]`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dv_fderiv_conj_holomorphic_eq_zero {n : ℕ} {c : V n → ℂ} {y : V n} (hc : DifferentiableAt ℂ c y)
    (ζ : V n) : dv (fderiv ℝ (fun v => conj (c v)) y) ζ = 0 := by
  have h := (hc.restrictScalars ℝ).hasFDerivAt.star
  have hL : fderiv ℂ c y (I • ζ) = I * fderiv ℂ c y ζ := by rw [map_smul, smul_eq_mul]
  have hfun : (fun v => conj (c v)) = fun v => star (c v) := rfl
  rw [hfun, h.fderiv, hc.fderiv_restrictScalars ℝ]
  simp only [dv, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', hL]
  simp only [ContinuousLinearEquiv.coe_coe, starL'_apply, star_mul', Complex.star_def,
    Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/- English proof (translation)
Simplify using `only [dv, ContinuousLinearMap.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dv_add' {n : ℕ} (L M : V n →L[ℝ] ℂ) (ζ : V n) :
    dv (L + M) ζ = dv L ζ + dv M ζ := by
  simp only [dv, ContinuousLinearMap.add_apply]
  ring

/- English proof (translation)
Simplify using `only [dv, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
private theorem dv_sum_smul {n : ℕ} (a : Fin n → ℂ) (L : Fin n → V n →L[ℝ] ℂ) (ζ : V n) :
    dv (∑ k, a k • L k) ζ = ∑ k, a k * dv (L k) ζ := by
  simp only [dv, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Establish `hΦR : ContDiffAt ℝ 2 Φ y` using `hΦ.restrict_scalars ℝ`. Rewrite using `[leviV_eq_dv (hf.comp y hΦR) ξ, leviV_eq_dv hf]`. Simplify using `only [WithLp.toLp_ofLp]`. Establish `hfF : DifferentiableAt ℝ (fderiv ℝ f) (Φ y)` using `(hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hA : ∀ k, DifferentiableAt ℝ (wdb n k f) (Φ y)`.

Introduce `k`. Unfold `wdb`. Establish `h1 : DifferentiableAt ℝ (fun v => fderiv ℝ f v (bas n k)) (Φ y)` using `hfF.clm_apply (differentiableAt_const _)`. Establish `h2 : DifferentiableAt ℝ (fun v => fderiv ℝ f v (I • bas n k)) (Φ y)` using `hfF.clm_apply (differentiableAt_const _)`. Establish `h3 : DifferentiableAt ℝ (fun v => fderiv ℝ f v (bas n k) + I * fderiv ℝ f v (I • bas n k)) (Φ y)` using `h1.add (h2.const_mul I)`.

Simplify `h3.mul_const (2⁻¹ : ℂ)` using `only [div_eq_mul_inv]`. Establish `hΦd : DifferentiableAt ℂ Φ y` using `hΦ.differentiableAt (by norm_num)`. Establish `hDΦ : DifferentiableAt ℂ (fderiv ℂ Φ) y` using `(hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hc : ∀ k, DifferentiableAt ℂ (fun v => (fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k) y` using `fun k => (EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiableAt.comp y (hDΦ.clm_apply (differentiableAt_const _))`. Establish `hev : (fun v => dbv (fderiv ℝ (f ∘ Φ) v) (WithLp.toLp 2 ξ)) =ᶠ[𝓝 y] fun v => ∑ k, wdb n k f (Φ v) * conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k)`.

Establish `h1 : ∀ᶠ v in 𝓝 y, ContDiffAt ℝ 2 f (Φ v)` using `hΦd.continuousAt.eventually (hf.eventually (by simp))`. Establish `h2 : ∀ᶠ v in 𝓝 y, ContDiffAt ℂ 2 Φ v` using `hΦ.eventually (by simp)`. Use `filter_upwards [h1, h2] with v hv1 hv2`. Rewrite using `[dbv_comp (hv1.differentiableAt (by norm_num)) (hv2.differentiableAt (by norm_num)), ← sum_wdb_eq]`. Establish `hK : HasFDerivAt (fun v => ∑ k, wdb n k f (Φ v) * conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k)) (∑ k, (wdb n k f (Φ y) • fderiv ℝ (fun v => conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k)) y + conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k) • fderiv ℝ (wdb n k f ∘ Φ) y)) y`.

Use `HasFDerivAt.fun_sum fun k _ => ?_` and prove the remaining obligations. Establish `ha : HasFDerivAt (wdb n k f ∘ Φ) (fderiv ℝ (wdb n k f ∘ Φ) y) y` using `((hA k).comp y (hΦd.restrictScalars ℝ)).hasFDerivAt`. Establish `hb : HasFDerivAt (fun v => conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k)) (fderiv ℝ (fun v => conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k)) y) y` using `((hc k).restrictScalars ℝ).star.hasFDerivAt`. Conclude with `ha.mul hb`. Establish `hR : (fun w => dbv (fderiv ℝ f w) (fderiv ℂ Φ y (WithLp.toLp 2 ξ))) = fun w => ∑ k, wdb n k f w * conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k)`.

Use function extensionality and compare the values at `w`. Rewrite using `[← sum_wdb_eq]`. Establish `hRD : HasFDerivAt (fun w => ∑ k, wdb n k f w * conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k)) (∑ k, conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k) • fderiv ℝ (wdb n k f) (Φ y)) (Φ y)` using `HasFDerivAt.fun_sum fun k _ => (hA k).hasFDerivAt.mul_const _`. Rewrite using `[hev.fderiv_eq, hK.fderiv, hR, hRD.fderiv, Finset.sum_add_distrib, dv_add', dv_sum_smul, dv_sum_smul, dv_sum_smul]`. Simplify using `only [dv_fderiv_conj_holomorphic_eq_zero (hc _), mul_zero, Finset.sum_const_zero, zero_add]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[dv_fderiv_comp_holomorphic (hA k) hΦd]`.
-/
theorem leviV_comp {n : ℕ} {f : V n → ℂ} {Φ : V n → V n} {y : V n}
    (hf : ContDiffAt ℝ 2 f (Φ y)) (hΦ : ContDiffAt ℂ 2 Φ y) (ξ : Fin n → ℂ) :
    leviV n (f ∘ Φ) y ξ = leviV n f (Φ y) (fderiv ℂ Φ y (WithLp.toLp 2 ξ)).ofLp := by
  have hΦR : ContDiffAt ℝ 2 Φ y := hΦ.restrict_scalars ℝ
  rw [leviV_eq_dv (hf.comp y hΦR) ξ, leviV_eq_dv hf]
  simp only [WithLp.toLp_ofLp]
  have hfF : DifferentiableAt ℝ (fderiv ℝ f) (Φ y) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : ∀ k, DifferentiableAt ℝ (wdb n k f) (Φ y) := by
    intro k
    unfold wdb
    have h1 : DifferentiableAt ℝ (fun v => fderiv ℝ f v (bas n k)) (Φ y) :=
      hfF.clm_apply (differentiableAt_const _)
    have h2 : DifferentiableAt ℝ (fun v => fderiv ℝ f v (I • bas n k)) (Φ y) :=
      hfF.clm_apply (differentiableAt_const _)
    have h3 : DifferentiableAt ℝ
        (fun v => fderiv ℝ f v (bas n k) + I * fderiv ℝ f v (I • bas n k)) (Φ y) :=
      h1.add (h2.const_mul I)
    simpa only [div_eq_mul_inv] using h3.mul_const (2⁻¹ : ℂ)
  have hΦd : DifferentiableAt ℂ Φ y := hΦ.differentiableAt (by norm_num)
  have hDΦ : DifferentiableAt ℂ (fderiv ℂ Φ) y :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : ∀ k, DifferentiableAt ℂ (fun v => (fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k) y := fun k =>
    (EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiableAt.comp y
      (hDΦ.clm_apply (differentiableAt_const _))
  have hev : (fun v => dbv (fderiv ℝ (f ∘ Φ) v) (WithLp.toLp 2 ξ)) =ᶠ[𝓝 y]
      fun v => ∑ k, wdb n k f (Φ v) * conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k) := by
    have h1 : ∀ᶠ v in 𝓝 y, ContDiffAt ℝ 2 f (Φ v) :=
      hΦd.continuousAt.eventually (hf.eventually (by simp))
    have h2 : ∀ᶠ v in 𝓝 y, ContDiffAt ℂ 2 Φ v := hΦ.eventually (by simp)
    filter_upwards [h1, h2] with v hv1 hv2
    rw [dbv_comp (hv1.differentiableAt (by norm_num)) (hv2.differentiableAt (by norm_num)),
      ← sum_wdb_eq]
  have hK : HasFDerivAt
      (fun v => ∑ k, wdb n k f (Φ v) * conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k))
      (∑ k, (wdb n k f (Φ y) • fderiv ℝ (fun v => conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k)) y +
        conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k) • fderiv ℝ (wdb n k f ∘ Φ) y)) y := by
    refine HasFDerivAt.fun_sum fun k _ => ?_
    have ha : HasFDerivAt (wdb n k f ∘ Φ) (fderiv ℝ (wdb n k f ∘ Φ) y) y :=
      ((hA k).comp y (hΦd.restrictScalars ℝ)).hasFDerivAt
    have hb : HasFDerivAt (fun v => conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k))
        (fderiv ℝ (fun v => conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k)) y) y :=
      ((hc k).restrictScalars ℝ).star.hasFDerivAt
    exact ha.mul hb
  have hR : (fun w => dbv (fderiv ℝ f w) (fderiv ℂ Φ y (WithLp.toLp 2 ξ))) =
      fun w => ∑ k, wdb n k f w * conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k) := by
    funext w
    rw [← sum_wdb_eq]
  have hRD : HasFDerivAt (fun w => ∑ k, wdb n k f w * conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k))
      (∑ k, conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k) • fderiv ℝ (wdb n k f) (Φ y)) (Φ y) :=
    HasFDerivAt.fun_sum fun k _ => (hA k).hasFDerivAt.mul_const _
  rw [hev.fderiv_eq, hK.fderiv, hR, hRD.fderiv, Finset.sum_add_distrib, dv_add', dv_sum_smul,
    dv_sum_smul, dv_sum_smul]
  simp only [dv_fderiv_conj_holomorphic_eq_zero (hc _), mul_zero, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dv_fderiv_comp_holomorphic (hA k) hΦd]

end

end ReciprocityTheory.L2DbarEstimates.Y
