import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaWeightStatement
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Matrix

open Complex ComplexConjugate Filter Topology Matrix

namespace ReciprocityTheory.L2DbarEstimates.H

open ReciprocityTheory.L2DbarEstimates

def LeviChainStatement : Prop :=
  ∀ (n : ℕ) (k : ℝ → ℝ) (v : V n → ℝ) (x : V n) (ξ : Fin n → ℂ),
    ContDiffAt ℝ 2 v x → ContDiffAt ℝ 2 k (v x) →
    leviV n (fun y => ((k (v y) : ℝ) : ℂ)) x ξ =
      ((deriv k (v x) : ℝ) : ℂ) * leviV n (fun y => ((v y : ℝ) : ℂ)) x ξ +
      ((deriv (deriv k) (v x) : ℝ) : ℂ) *
        ((Complex.normSq (∑ j, wd n j (fun y => ((v y : ℝ) : ℂ)) x * ξ j) : ℝ) : ℂ)

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[← Complex.mul_conj, map_sum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ofReal_normSq_sum_mul (a ξ : Fin n → ℂ) :
    ((Complex.normSq (∑ j, a j * ξ j) : ℝ) : ℂ) =
      ∑ j, ∑ kk, a j * conj (a kk) * ξ j * conj (ξ kk) := by
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  ring

/- English proof (translation)
Introduce `n k v x ξ hv hk`. Establish `hv1 : DifferentiableAt ℝ v x` using `hv.differentiableAt (by simp)`. Establish `hk1 : DifferentiableAt ℝ (deriv k) (v x)` using `differentiableAt_deriv_of_contDiffAt hk`. Establish `hv' : ContDiffAt ℝ 2 (fun y => ((v y : ℝ) : ℂ)) x` using `ofRealCLM.contDiff.contDiffAt.comp x hv`. Establish `hvd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y` using `eventually_differentiableAt_of_contDiffAt hv`.

Establish `hkd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ k (v y)` using `hv1.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hk)`. Establish `hE : ∀ kk : Fin n, wdb n kk (fun y => ((k (v y) : ℝ) : ℂ)) =ᶠ[𝓝 x] fun y => ((deriv k (v y) : ℝ) : ℂ) * wdb n kk (fun y => ((v y : ℝ) : ℂ)) y`. Introduce `kk`. Use `filter_upwards [hvd, hkd] with y hy1 hy2`. Conclude with `wdb_ofReal_comp hy2 hy1`.

Establish `hD1 : DifferentiableAt ℝ (fun y => ((deriv k (v y) : ℝ) : ℂ)) x` using `differentiableAt_ofReal (hk1.comp x hv1)`. Establish `hterm : ∀ j kk : Fin n, wd n j (wdb n kk (fun y => ((k (v y) : ℝ) : ℂ))) x = ((deriv (deriv k) (v x) : ℝ) : ℂ) * wd n j (fun y => ((v y : ℝ) : ℂ)) x * conj (wd n kk (fun y => ((v y : ℝ) : ℂ)) x) + ((deriv k (v x) : ℝ) : ℂ) * wd n j (wdb n kk (fun y => ((v y : ℝ) : ℂ))) x`. Introduce `j kk`. Rewrite using `[wd_congr (hE kk), wd_mul (f := fun y => ((deriv k (v y) : ℝ) : ℂ)) (g := wdb n kk (fun y => ((v y : ℝ) : ℂ))) hD1 (differentiableAt_wdb hv'), wd_ofReal_comp hk1 hv1, wdb_ofReal hv1]`. Rewrite using `[ofReal_normSq_sum_mul]`.

Simplify using `only [leviV, hterm, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun kk _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem leviChain : LeviChainStatement := by
  intro n k v x ξ hv hk
  have hv1 : DifferentiableAt ℝ v x := hv.differentiableAt (by simp)
  have hk1 : DifferentiableAt ℝ (deriv k) (v x) := differentiableAt_deriv_of_contDiffAt hk
  have hv' : ContDiffAt ℝ 2 (fun y => ((v y : ℝ) : ℂ)) x :=
    ofRealCLM.contDiff.contDiffAt.comp x hv
  have hvd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y := eventually_differentiableAt_of_contDiffAt hv
  have hkd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ k (v y) :=
    hv1.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hk)
  have hE : ∀ kk : Fin n, wdb n kk (fun y => ((k (v y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => ((deriv k (v y) : ℝ) : ℂ) * wdb n kk (fun y => ((v y : ℝ) : ℂ)) y := by
    intro kk
    filter_upwards [hvd, hkd] with y hy1 hy2
    exact wdb_ofReal_comp hy2 hy1
  have hD1 : DifferentiableAt ℝ (fun y => ((deriv k (v y) : ℝ) : ℂ)) x :=
    differentiableAt_ofReal (hk1.comp x hv1)
  have hterm : ∀ j kk : Fin n, wd n j (wdb n kk (fun y => ((k (v y) : ℝ) : ℂ))) x =
      ((deriv (deriv k) (v x) : ℝ) : ℂ) * wd n j (fun y => ((v y : ℝ) : ℂ)) x *
          conj (wd n kk (fun y => ((v y : ℝ) : ℂ)) x) +
        ((deriv k (v x) : ℝ) : ℂ) * wd n j (wdb n kk (fun y => ((v y : ℝ) : ℂ))) x := by
    intro j kk
    rw [wd_congr (hE kk),
      wd_mul (f := fun y => ((deriv k (v y) : ℝ) : ℂ)) (g := wdb n kk (fun y => ((v y : ℝ) : ℂ)))
        hD1 (differentiableAt_wdb hv'),
      wd_ofReal_comp hk1 hv1, wdb_ofReal hv1]
  rw [ofReal_normSq_sum_mul]
  simp only [leviV, hterm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun kk _ => ?_
  ring

/- English proof (translation)
Establish `hfun : (fun y => ((∑ i, u i y : ℝ) : ℂ)) = fun y => ∑ i, ((u i y : ℝ) : ℂ)`. Use function extensionality and compare the values at `y`. Conclude with `Complex.ofReal_sum _ _`. Establish `hd : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (fun y => ((u i y : ℝ) : ℂ)) x` using `fun i _ => Complex.ofRealCLM.differentiableAt.comp x (hu i)`. Unfold `wd`.

Rewrite using `[hfun]`. Use `first`. Consider the case `rw [fderiv_fun_sum hd]`. Consider the case `rw [fderiv_sum' hd]`. Simplify using `only [ContinuousLinearMap.sum_apply]`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]`.
-/
theorem wd_ofReal_sum {m : ℕ} {j : Fin n} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) :
    wd n j (fun y => ((∑ i, u i y : ℝ) : ℂ)) x = ∑ i, wd n j (fun y => (u i y : ℂ)) x := by
  have hfun : (fun y => ((∑ i, u i y : ℝ) : ℂ)) = fun y => ∑ i, ((u i y : ℝ) : ℂ) := by
    funext y
    exact Complex.ofReal_sum _ _
  have hd : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (fun y => ((u i y : ℝ) : ℂ)) x :=
    fun i _ => Complex.ofRealCLM.differentiableAt.comp x (hu i)
  unfold wd
  rw [hfun]
  first
  | rw [fderiv_fun_sum hd]
  | rw [fderiv_sum' hd]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

/- English proof (translation)
Establish `hd : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (G i) x` using `fun i _ => hG i`. Unfold `wd`. Use `first`. Consider the case `rw [fderiv_fun_sum hd]`. Consider the case `rw [fderiv_sum hd]`.

Simplify using `only [ContinuousLinearMap.sum_apply]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]`.
-/
private theorem wd_wdb_finset_sum {m : ℕ} {j : Fin n} {G : Fin m → V n → ℂ} {x : V n}
    (hG : ∀ i, DifferentiableAt ℝ (G i) x) :
    wd n j (fun y => ∑ i, G i y) x = ∑ i, wd n j (G i) x := by
  have hd : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (G i) x := fun i _ => hG i
  unfold wd
  first
  | rw [fderiv_fun_sum hd]
  | rw [fderiv_sum hd]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

/- English proof (translation)
Establish `hd : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (G i) x` using `fun i _ => hG i`. Unfold `wdb`. Use `first`. Consider the case `rw [fderiv_fun_sum hd]`. Consider the case `rw [fderiv_sum hd]`.

Simplify using `only [ContinuousLinearMap.sum_apply]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]`.
-/
private theorem wdb_sum' {m : ℕ} {k : Fin n} {G : Fin m → V n → ℂ} {x : V n}
    (hG : ∀ i, DifferentiableAt ℝ (G i) x) :
    wdb n k (fun y => ∑ i, G i y) x = ∑ i, wdb n k (G i) x := by
  have hd : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (G i) x := fun i _ => hG i
  unfold wdb
  first
  | rw [fderiv_fun_sum hd]
  | rw [fderiv_sum hd]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]

/- English proof (translation)
Unfold `wd`. Rewrite using `[h.fderiv_eq]`.
-/
private theorem wd_apply_congr_of_eventuallyEq {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wd n j f x = wd n j g x := by
  unfold wd
  rw [h.fderiv_eq]

/- English proof (translation)
Apply the tactic sequence `have h1 : ContDiffAt ℝ 1 (fderiv ℝ U) x := hU.fderiv_right (by first | norm_num | rfl | simp)`. Establish `h2 : DifferentiableAt ℝ (fderiv ℝ U) x` using `h1.differentiableAt one_ne_zero`. Unfold `wdb`. Establish `h3 : DifferentiableAt ℝ (fun y => fderiv ℝ U y (bas n k)) x` using `h2.clm_apply (differentiableAt_const _)`. Establish `h4 : DifferentiableAt ℝ (fun y => fderiv ℝ U y (Complex.I • bas n k)) x` using `h2.clm_apply (differentiableAt_const _)`.

Establish `h5 : DifferentiableAt ℝ (fun y => fderiv ℝ U y (bas n k) + Complex.I * fderiv ℝ U y (Complex.I • bas n k)) x` using `h3.add (h4.const_mul Complex.I)`. Use `first`. Consider the case `fun_prop`. Consider the case `exact h5.div_const (2 : ℂ)`. Consider the case `exact (h5.mul_const ((2 : ℂ)⁻¹)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => div_eq_mul_inv _ _)`.
-/
private theorem wdb_differentiableAt_of_contDiffAt_two {k : Fin n} {U : V n → ℂ} {x : V n} (hU : ContDiffAt ℝ 2 U x) :
    DifferentiableAt ℝ (wdb n k U) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ U) x :=
    hU.fderiv_right (by first | norm_num | rfl | simp)
  have h2 : DifferentiableAt ℝ (fderiv ℝ U) x := h1.differentiableAt one_ne_zero
  unfold wdb
  have h3 : DifferentiableAt ℝ (fun y => fderiv ℝ U y (bas n k)) x :=
    h2.clm_apply (differentiableAt_const _)
  have h4 : DifferentiableAt ℝ (fun y => fderiv ℝ U y (Complex.I • bas n k)) x :=
    h2.clm_apply (differentiableAt_const _)
  have h5 : DifferentiableAt ℝ (fun y => fderiv ℝ U y (bas n k) +
      Complex.I * fderiv ℝ U y (Complex.I • bas n k)) x := h3.add (h4.const_mul Complex.I)
  first
  | fun_prop
  | exact h5.div_const (2 : ℂ)
  | exact (h5.mul_const ((2 : ℂ)⁻¹)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => div_eq_mul_inv _ _)

/- English proof (translation)
Establish `hU : ∀ i, ContDiffAt ℝ 2 (fun y => ((u i y : ℝ) : ℂ)) x` using `fun i => Complex.ofRealCLM.contDiff.contDiffAt.comp x (hu i)`. Establish `hfun : (fun y => ((∑ i, u i y : ℝ) : ℂ)) = fun y => ∑ i, ((u i y : ℝ) : ℂ)`. Use function extensionality and compare the values at `y`. Conclude with `Complex.ofReal_sum _ _`. Establish `hev : ∀ᶠ y in 𝓝 x, ∀ i, DifferentiableAt ℝ (fun y => ((u i y : ℝ) : ℂ)) y`.

Rewrite using `[Filter.eventually_all]`. Introduce `i`. Apply the tactic sequence `filter_upwards [(hU i).eventually (by first | simp | decide | norm_num)] with y hy`. Apply the tactic sequence `exact hy.differentiableAt (by first | norm_num | simp | exact one_le_two)`. Establish `hwdb : ∀ k, wdb n k (fun y => ∑ i, ((u i y : ℝ) : ℂ)) =ᶠ[𝓝 x] fun y => ∑ i, wdb n k (fun y => ((u i y : ℝ) : ℂ)) y`.

Introduce `k`. Use `filter_upwards [hev] with y hy`. Conclude with `wdb_sum' hy`. Establish `hterm : ∀ j k, wd n j (wdb n k (fun y => ((∑ i, u i y : ℝ) : ℂ))) x = ∑ i, wd n j (wdb n k (fun y => ((u i y : ℝ) : ℂ))) x`. Introduce `j k`.

Rewrite using `[hfun, wd_apply_congr_of_eventuallyEq (hwdb k), wd_wdb_finset_sum fun i => wdb_differentiableAt_of_contDiffAt_two (hU i)]`. Unfold `leviV`. Simplify using `only [hterm, Finset.sum_mul]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`.
-/
theorem leviV_ofReal_sum {m : ℕ} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, ContDiffAt ℝ 2 (u i) x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((∑ i, u i y : ℝ) : ℂ)) x ξ = ∑ i, leviV n (fun y => (u i y : ℂ)) x ξ := by
  have hU : ∀ i, ContDiffAt ℝ 2 (fun y => ((u i y : ℝ) : ℂ)) x :=
    fun i => Complex.ofRealCLM.contDiff.contDiffAt.comp x (hu i)
  have hfun : (fun y => ((∑ i, u i y : ℝ) : ℂ)) = fun y => ∑ i, ((u i y : ℝ) : ℂ) := by
    funext y
    exact Complex.ofReal_sum _ _
  have hev : ∀ᶠ y in 𝓝 x, ∀ i, DifferentiableAt ℝ (fun y => ((u i y : ℝ) : ℂ)) y := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [(hU i).eventually (by first | simp | decide | norm_num)] with y hy
    exact hy.differentiableAt (by first | norm_num | simp | exact one_le_two)
  have hwdb : ∀ k, wdb n k (fun y => ∑ i, ((u i y : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => ∑ i, wdb n k (fun y => ((u i y : ℝ) : ℂ)) y := by
    intro k
    filter_upwards [hev] with y hy
    exact wdb_sum' hy
  have hterm : ∀ j k, wd n j (wdb n k (fun y => ((∑ i, u i y : ℝ) : ℂ))) x =
      ∑ i, wd n j (wdb n k (fun y => ((u i y : ℝ) : ℂ))) x := by
    intro j k
    rw [hfun, wd_apply_congr_of_eventuallyEq (hwdb k), wd_wdb_finset_sum fun i => wdb_differentiableAt_of_contDiffAt_two (hU i)]
  unfold leviV
  simp only [hterm, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

noncomputable def wJac (n p : ℕ) (g : Fin p → V n → ℂ) (x : V n) : Matrix (Fin p) (Fin n) ℂ :=
  fun i k => wd n k (g i) x

def LeviLogNormSqStatement : Prop :=
  ∀ (n p : ℕ) (g : Fin p → V n → ℂ) (x : V n) (ξ : Fin n → ℂ),
    (∀ i, ContDiffAt ℂ 2 (g i) x) → (fun i => g i x) ≠ 0 →
    leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((sqNorm (projPerp (fun i => g i x) *ᵥ (wJac n p g x *ᵥ ξ)) / sqNorm (fun i => g i x) : ℝ) : ℂ)

/- English proof (translation)
Establish `h1 : ContDiffAt ℝ 2 g x` using `hg.restrict_scalars ℝ`. Establish `h2 : ContDiffAt ℝ 2 (fun y => ‖g y‖ ^ 2) x` using `by first`. Consider the case `exact (contDiff_norm_sq ℝ).contDiffAt.comp x h1`. Consider the case `exact (contDiff_norm_sq ℂ).contDiffAt.comp x h1`. Use `h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Conclude with `Complex.normSq_eq_norm_sq _`.
-/
theorem contDiffAt_normSq_comp {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    ContDiffAt ℝ 2 (fun y => Complex.normSq (g y)) x := by
  have h1 : ContDiffAt ℝ 2 g x := hg.restrict_scalars ℝ
  have h2 : ContDiffAt ℝ 2 (fun y => ‖g y‖ ^ 2) x := by
    first
    | exact (contDiff_norm_sq ℝ).contDiffAt.comp x h1
    | exact (contDiff_norm_sq ℂ).contDiffAt.comp x h1
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  exact Complex.normSq_eq_norm_sq _

/- English proof (translation)
Apply the tactic sequence `have hdiff : DifferentiableAt ℂ g x := hg.differentiableAt (by first | norm_num | exact one_le_two | decide | simp)`. Establish `hD : HasFDerivAt g (fderiv ℝ g x) x` using `(hdiff.restrictScalars ℝ).hasFDerivAt`. Establish `hlin : ∀ v : V n, fderiv ℝ g x (Complex.I • v) = Complex.I * fderiv ℝ g x v`. Introduce `v`. Rewrite using `[hdiff.fderiv_restrictScalars ℝ]`.

Simplify using `only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]`. Establish `hc : HasFDerivAt (fun y => conj (g y)) ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g x)) x` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x hD`. Establish `hh : HasFDerivAt (fun y => g y * conj (g y)) (g x • (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g x) + conj (g x) • fderiv ℝ g x) x` using `hD.mul hc`. Establish `hfun : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y)`. Use function extensionality and compare the values at `y`.

Conclude with `(Complex.mul_conj (g y)).symm`. Unfold `wd`. Rewrite using `[hfun, hh.fderiv]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul, hlin, map_mul, Complex.conj_I]`. Take the linear combination `(g x * conj (fderiv ℝ g x (bas n j)) / 2) * Complex.I_mul_I`.
-/
theorem wd_normSq_comp {j : Fin n} {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    wd n j (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x = wd n j g x * conj (g x) := by
  have hdiff : DifferentiableAt ℂ g x :=
    hg.differentiableAt (by first | norm_num | exact one_le_two | decide | simp)
  have hD : HasFDerivAt g (fderiv ℝ g x) x := (hdiff.restrictScalars ℝ).hasFDerivAt
  have hlin : ∀ v : V n, fderiv ℝ g x (Complex.I • v) = Complex.I * fderiv ℝ g x v := by
    intro v
    rw [hdiff.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hc : HasFDerivAt (fun y => conj (g y))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g x)) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x hD
  have hh : HasFDerivAt (fun y => g y * conj (g y))
      (g x • (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g x) + conj (g x) • fderiv ℝ g x) x :=
    hD.mul hc
  have hfun : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y
    exact (Complex.mul_conj (g y)).symm
  unfold wd
  rw [hfun, hh.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, hlin, map_mul, Complex.conj_I]
  linear_combination (g x * conj (fderiv ℝ g x (bas n j)) / 2) * Complex.I_mul_I

/- English proof (translation)
Establish `hlin : fderiv ℝ g y (Complex.I • bas n j) = Complex.I * fderiv ℝ g y (bas n j)`. Rewrite using `[hy.fderiv_restrictScalars ℝ]`. Simplify using `only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]`. Unfold `wd`. Rewrite using `[hlin]`.

Take the linear combination `(-(fderiv ℝ g y (bas n j)) / 2) * Complex.I_mul_I`.
-/
private theorem wd_eq_fderiv_basis_of_differentiableAt {j : Fin n} {g : V n → ℂ} {y : V n} (hy : DifferentiableAt ℂ g y) :
    wd n j g y = fderiv ℝ g y (bas n j) := by
  have hlin : fderiv ℝ g y (Complex.I • bas n j) = Complex.I * fderiv ℝ g y (bas n j) := by
    rw [hy.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  unfold wd
  rw [hlin]
  linear_combination (-(fderiv ℝ g y (bas n j)) / 2) * Complex.I_mul_I

/- English proof (translation)
Establish `hD : HasFDerivAt g (fderiv ℝ g y) y` using `(hy.restrictScalars ℝ).hasFDerivAt`. Establish `hlin : ∀ v : V n, fderiv ℝ g y (Complex.I • v) = Complex.I * fderiv ℝ g y v`. Introduce `v`. Rewrite using `[hy.fderiv_restrictScalars ℝ]`. Simplify using `only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]`.

Establish `hc : HasFDerivAt (fun y => conj (g y)) ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g y)) y` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp y hD`. Establish `hh : HasFDerivAt (fun y => g y * conj (g y)) (g y • (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g y) + conj (g y) • fderiv ℝ g y) y` using `hD.mul hc`. Establish `hfun : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y)`. Use function extensionality and compare the values at `y`. Conclude with `(Complex.mul_conj (g y)).symm`.

Rewrite using `[wd_eq_fderiv_basis_of_differentiableAt hy]`. Unfold `wdb`. Rewrite using `[hfun, hh.fderiv]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul, hlin, map_mul, Complex.conj_I]`. Take the linear combination `((conj (g y) * fderiv ℝ g y (bas n k) - g y * conj (fderiv ℝ g y (bas n k))) / 2) * Complex.I_mul_I`.
-/
private theorem wdb_normSq_eq_mul_conj_wd {k : Fin n} {g : V n → ℂ} {y : V n} (hy : DifferentiableAt ℂ g y) :
    wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) y = g y * conj (wd n k g y) := by
  have hD : HasFDerivAt g (fderiv ℝ g y) y := (hy.restrictScalars ℝ).hasFDerivAt
  have hlin : ∀ v : V n, fderiv ℝ g y (Complex.I • v) = Complex.I * fderiv ℝ g y v := by
    intro v
    rw [hy.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hc : HasFDerivAt (fun y => conj (g y))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g y)) y :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp y hD
  have hh : HasFDerivAt (fun y => g y * conj (g y))
      (g y • (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g y) + conj (g y) • fderiv ℝ g y) y :=
    hD.mul hc
  have hfun : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y
    exact (Complex.mul_conj (g y)).symm
  rw [wd_eq_fderiv_basis_of_differentiableAt hy]
  unfold wdb
  rw [hfun, hh.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, hlin, map_mul, Complex.conj_I]
  linear_combination ((conj (g y) * fderiv ℝ g y (bas n k) -
    g y * conj (fderiv ℝ g y (bas n k))) / 2) * Complex.I_mul_I

/- English proof (translation)
Establish `hD : HasFDerivAt g (fderiv ℝ g x) x` using `hg.hasFDerivAt`. Establish `hH : HasFDerivAt h (fderiv ℝ h x) x` using `(hh.restrictScalars ℝ).hasFDerivAt`. Establish `hlin : ∀ v : V n, fderiv ℝ h x (Complex.I • v) = Complex.I * fderiv ℝ h x v`. Introduce `v`. Rewrite using `[hh.fderiv_restrictScalars ℝ]`.

Simplify using `only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]`. Establish `hc : HasFDerivAt (fun y => conj (h y)) ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ h x)) x` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x hH`. Establish `hp : HasFDerivAt (fun y => g y * conj (h y)) (g x • (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ h x) + conj (h x) • fderiv ℝ g x) x` using `hD.mul hc`. Unfold `wd`. Rewrite using `[hp.fderiv]`.

Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul, hlin, map_mul, Complex.conj_I]`. Take the linear combination `(g x * conj (fderiv ℝ h x (bas n j)) / 2) * Complex.I_mul_I`.
-/
private theorem wd_mul_conj_of_differentiableAt {j : Fin n} {g h : V n → ℂ} {x : V n}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℂ h x) :
    wd n j (fun y => g y * conj (h y)) x = wd n j g x * conj (h x) := by
  have hD : HasFDerivAt g (fderiv ℝ g x) x := hg.hasFDerivAt
  have hH : HasFDerivAt h (fderiv ℝ h x) x := (hh.restrictScalars ℝ).hasFDerivAt
  have hlin : ∀ v : V n, fderiv ℝ h x (Complex.I • v) = Complex.I * fderiv ℝ h x v := by
    intro v
    rw [hh.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hc : HasFDerivAt (fun y => conj (h y))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ h x)) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x hH
  have hp : HasFDerivAt (fun y => g y * conj (h y))
      (g x • (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ h x) + conj (h x) • fderiv ℝ g x) x :=
    hD.mul hc
  unfold wd
  rw [hp.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, hlin, map_mul, Complex.conj_I]
  linear_combination (g x * conj (fderiv ℝ h x (bas n j)) / 2) * Complex.I_mul_I

/- English proof (translation)
Apply the tactic sequence `have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y := by filter_upwards [hg.eventually (by first | simp | decide | norm_num)] with y hy`. Apply the tactic sequence `exact hy.differentiableAt (by first | norm_num | simp)`. Establish `hdx : DifferentiableAt ℂ g x` using `hev.self_of_nhds`. Establish `hhol : ∀ k, DifferentiableAt ℂ (wd n k g) x`. Introduce `k`.

Apply the tactic sequence `have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by first | norm_num | rfl | simp)`. Establish `h2 : DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n k)) x` using `(h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)`. Use `h2.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hev] with y hy`. Rewrite using `[wd_eq_fderiv_basis_of_differentiableAt hy, hy.fderiv_restrictScalars ℝ]`.

Both sides reduce to the same expression. Establish `hterm : ∀ j k, wd n j (wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x = wd n j g x * conj (wd n k g x)`. Introduce `j k`. Establish `hc : wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) =ᶠ[𝓝 x] fun y => g y * conj (wd n k g y)` using `by filter_upwards [hev] with y hy`. Conclude with `wdb_normSq_eq_mul_conj_wd hy`.

Rewrite using `[wd_apply_congr_of_eventuallyEq hc, wd_mul_conj_of_differentiableAt (hdx.restrictScalars ℝ) (hhol k)]`. Unfold `leviV`. Simplify using `only [hterm]`. Rewrite using `[ofReal_normSq_sum_mul]`.
-/
theorem leviV_normSq_comp {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x ξ =
      ((Complex.normSq (∑ j, wd n j g x * ξ j) : ℝ) : ℂ) := by
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y := by
    filter_upwards [hg.eventually (by first | simp | decide | norm_num)] with y hy
    exact hy.differentiableAt (by first | norm_num | simp)
  have hdx : DifferentiableAt ℂ g x := hev.self_of_nhds
  have hhol : ∀ k, DifferentiableAt ℂ (wd n k g) x := by
    intro k
    have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by first | norm_num | rfl | simp)
    have h2 : DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n k)) x :=
      (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    rw [wd_eq_fderiv_basis_of_differentiableAt hy, hy.fderiv_restrictScalars ℝ]
    rfl
  have hterm : ∀ j k, wd n j (wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x =
      wd n j g x * conj (wd n k g x) := by
    intro j k
    have hc : wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
        fun y => g y * conj (wd n k g y) := by
      filter_upwards [hev] with y hy
      exact wdb_normSq_eq_mul_conj_wd hy
    rw [wd_apply_congr_of_eventuallyEq hc, wd_mul_conj_of_differentiableAt (hdx.restrictScalars ℝ) (hhol k)]
  unfold leviV
  simp only [hterm]
  rw [ofReal_normSq_sum_mul]

/- English proof (translation)
Establish `hc : ∀ v : Fin p → ℂ, ((sqNorm v : ℝ) : ℂ) = ∑ i, v i * conj (v i)`. Introduce `v`. Unfold `sqNorm`. Rewrite using `[Complex.ofReal_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => (Complex.mul_conj _).symm`.

Establish `hpos : 0 < sqNorm G`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hG`. Unfold `sqNorm`. Conclude with `Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩`. Establish `hS0 : ((sqNorm G : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hpos.ne'`.

Establish `hP : ∀ i, (projPerp G *ᵥ w) i = w i - ((sqNorm G : ℝ) : ℂ)⁻¹ * (G i * ∑ j, conj (G j) * w j)`. Introduce `i`. Simplify using `only [projPerp, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]`. Use `congr 1`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hst : star (G j) = conj (G j)` using `rfl`. Rewrite using `[hst]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ i, (projPerp G *ᵥ w) i * conj ((projPerp G *ᵥ w) i) = w i * conj (w i) - ((sqNorm G : ℝ) : ℂ)⁻¹ * conj (∑ j, conj (G j) * w j) * (conj (G i) * w i) - ((sqNorm G : ℝ) : ℂ)⁻¹ * (∑ j, conj (G j) * w j) * (G i * conj (w i)) + ((sqNorm G : ℝ) : ℂ)⁻¹ * ((sqNorm G : ℝ) : ℂ)⁻¹ * …`.

Introduce `i`. Rewrite using `[hP i, map_sub, map_mul, map_mul, map_inv₀, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∑ i, G i * conj (w i) = conj (∑ j, conj (G j) * w j)`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Complex.conj_conj]`. Rewrite using `[hc (projPerp G *ᵥ w), hc w, ← Complex.mul_conj]`. Repeatedly rewrite using `[key]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h2, ← hc G]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ofReal_sqNorm_projPerp_mulVec {p : ℕ} (G w : Fin p → ℂ) (hG : G ≠ 0) :
    ((sqNorm (projPerp G *ᵥ w) : ℝ) : ℂ) = ((sqNorm w : ℝ) : ℂ) -
      ((Complex.normSq (∑ i, conj (G i) * w i) : ℝ) : ℂ) / ((sqNorm G : ℝ) : ℂ) := by
  have hc : ∀ v : Fin p → ℂ, ((sqNorm v : ℝ) : ℂ) = ∑ i, v i * conj (v i) := by
    intro v
    unfold sqNorm
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => (Complex.mul_conj _).symm
  have hpos : 0 < sqNorm G := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hG
    unfold sqNorm
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  have hS0 : ((sqNorm G : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hP : ∀ i, (projPerp G *ᵥ w) i =
      w i - ((sqNorm G : ℝ) : ℂ)⁻¹ * (G i * ∑ j, conj (G j) * w j) := by
    intro i
    simp only [projPerp, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hst : star (G j) = conj (G j) := rfl
    rw [hst]
    ring
  have key : ∀ i, (projPerp G *ᵥ w) i * conj ((projPerp G *ᵥ w) i) =
      w i * conj (w i)
        - ((sqNorm G : ℝ) : ℂ)⁻¹ * conj (∑ j, conj (G j) * w j) * (conj (G i) * w i)
        - ((sqNorm G : ℝ) : ℂ)⁻¹ * (∑ j, conj (G j) * w j) * (G i * conj (w i))
        + ((sqNorm G : ℝ) : ℂ)⁻¹ * ((sqNorm G : ℝ) : ℂ)⁻¹ * (∑ j, conj (G j) * w j) *
            conj (∑ j, conj (G j) * w j) * (G i * conj (G i)) := by
    intro i
    rw [hP i, map_sub, map_mul, map_mul, map_inv₀, Complex.conj_ofReal]
    ring
  have h2 : ∑ i, G i * conj (w i) = conj (∑ j, conj (G j) * w j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Complex.conj_conj]
  rw [hc (projPerp G *ᵥ w), hc w, ← Complex.mul_conj]
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h2, ← hc G]
  field_simp
  ring

/- English proof (translation)
Introduce `n p g x ξ hg hne`. Establish `hSi : ∀ i, ContDiffAt ℝ 2 (fun y => Complex.normSq (g i y)) x` using `fun i => contDiffAt_normSq_comp (hg i)`. Establish `hS : ContDiffAt ℝ 2 (fun y => sqNorm (fun i => g i y)) x`. Unfold `sqNorm`. Conclude with `ContDiffAt.sum fun i _ => hSi i`.

Establish `hSx : 0 < sqNorm (fun i => g i x)`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hne`. Unfold `sqNorm`. Conclude with `Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩`. Establish `hS0 : ((sqNorm (fun i => g i x) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hSx.ne'`.

Establish `hlog : ContDiffAt ℝ 2 Real.log (sqNorm (fun i => g i x))` using `Real.contDiffAt_log.mpr hSx.ne'`. Establish `chain : leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ = ((deriv Real.log (sqNorm (fun i => g i x)) : ℝ) : ℂ) * leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ + ((deriv (deriv Real.log) (sqNorm (fun i => g i x)) : ℝ) : ℂ) * ((Complex.normSq (∑ j …` using `leviChain n Real.log (fun y => sqNorm (fun i => g i y)) x ξ hS hlog`. Establish `d1 : deriv Real.log (sqNorm fun i => g i x) = (sqNorm fun i => g i x)⁻¹` using `Real.deriv_log _`. Establish `d2 : deriv (deriv Real.log) (sqNorm fun i => g i x) = -((sqNorm fun i => g i x) ^ 2)⁻¹`. Rewrite using `[Real.deriv_log']`.

Conclude with `deriv_inv`. Establish `hwd : ∀ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x = ∑ i, wd n j (g i) x * conj (g i x)`. Introduce `j`. Unfold `sqNorm`. Apply the tactic sequence `rw [wd_ofReal_sum fun i => (hSi i).differentiableAt (by first | norm_num | simp)]`.

Conclude with `Finset.sum_congr rfl fun i _ => wd_normSq_comp (hg i)`. Establish `hlv : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ = ∑ i, ((Complex.normSq ((wJac n p g x *ᵥ ξ) i) : ℝ) : ℂ)`. Unfold `sqNorm`. Rewrite using `[leviV_ofReal_sum hSi ξ]`. Conclude with `Finset.sum_congr rfl fun i _ => leviV_normSq_comp (hg i) ξ`.

Establish `hs : ∑ j, (∑ i, wd n j (g i) x * conj (g i x)) * ξ j = ∑ i, conj (g i x) * (wJac n p g x *ᵥ ξ) i`. Simplify using `only [Matrix.mulVec, dotProduct, wJac, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hW : ((sqNorm (wJac n p g x *ᵥ ξ) : ℝ) : ℂ) = ∑ i, ((Complex.normSq ((wJac n p g x *ᵥ ξ) i) : ℝ) : ℂ)`. Unfold `sqNorm`. Rewrite using `[Complex.ofReal_sum]`. Rewrite using `[chain, d1, d2, hlv]`. Simplify using `only [hwd]`.

Rewrite using `[hs, Complex.ofReal_div, ofReal_sqNorm_projPerp_mulVec _ _ hne, hW]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem leviLogNormSq : LeviLogNormSqStatement := by
  intro n p g x ξ hg hne
  have hSi : ∀ i, ContDiffAt ℝ 2 (fun y => Complex.normSq (g i y)) x :=
    fun i => contDiffAt_normSq_comp (hg i)
  have hS : ContDiffAt ℝ 2 (fun y => sqNorm (fun i => g i y)) x := by
    unfold sqNorm
    exact ContDiffAt.sum fun i _ => hSi i
  have hSx : 0 < sqNorm (fun i => g i x) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    unfold sqNorm
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  have hS0 : ((sqNorm (fun i => g i x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hSx.ne'
  have hlog : ContDiffAt ℝ 2 Real.log (sqNorm (fun i => g i x)) :=
    Real.contDiffAt_log.mpr hSx.ne'
  have chain : leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((deriv Real.log (sqNorm (fun i => g i x)) : ℝ) : ℂ) *
          leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ +
        ((deriv (deriv Real.log) (sqNorm (fun i => g i x)) : ℝ) : ℂ) *
          ((Complex.normSq (∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j) :
            ℝ) : ℂ) :=
    leviChain n Real.log (fun y => sqNorm (fun i => g i y)) x ξ hS hlog
  have d1 : deriv Real.log (sqNorm fun i => g i x) = (sqNorm fun i => g i x)⁻¹ :=
    Real.deriv_log _
  have d2 : deriv (deriv Real.log) (sqNorm fun i => g i x) = -((sqNorm fun i => g i x) ^ 2)⁻¹ := by
    rw [Real.deriv_log']
    exact deriv_inv
  have hwd : ∀ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x =
      ∑ i, wd n j (g i) x * conj (g i x) := by
    intro j
    unfold sqNorm
    rw [wd_ofReal_sum fun i => (hSi i).differentiableAt (by first | norm_num | simp)]
    exact Finset.sum_congr rfl fun i _ => wd_normSq_comp (hg i)
  have hlv : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ =
      ∑ i, ((Complex.normSq ((wJac n p g x *ᵥ ξ) i) : ℝ) : ℂ) := by
    unfold sqNorm
    rw [leviV_ofReal_sum hSi ξ]
    exact Finset.sum_congr rfl fun i _ => leviV_normSq_comp (hg i) ξ
  have hs : ∑ j, (∑ i, wd n j (g i) x * conj (g i x)) * ξ j =
      ∑ i, conj (g i x) * (wJac n p g x *ᵥ ξ) i := by
    simp only [Matrix.mulVec, dotProduct, wJac, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hW : ((sqNorm (wJac n p g x *ᵥ ξ) : ℝ) : ℂ) =
      ∑ i, ((Complex.normSq ((wJac n p g x *ᵥ ξ) i) : ℝ) : ℂ) := by
    unfold sqNorm
    rw [Complex.ofReal_sum]
  rw [chain, d1, d2, hlv]
  simp only [hwd]
  rw [hs, Complex.ofReal_div, ofReal_sqNorm_projPerp_mulVec _ _ hne, hW]
  push_cast
  field_simp
  ring

end ReciprocityTheory.L2DbarEstimates.H
