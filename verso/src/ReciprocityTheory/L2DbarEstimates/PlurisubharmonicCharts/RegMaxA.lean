import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

def rmStep (t : ℝ) : ℝ := 2 * Real.smoothTransition (t + 1 / 2) - 1

/- English proof (translation)
Unfold `rmStep`. Conclude with `(contDiff_const.mul (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const))).sub contDiff_const`.
-/
lemma rmStep_contDiff : ContDiff ℝ ∞ rmStep := by
  unfold rmStep
  exact (contDiff_const.mul (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const))).sub
    contDiff_const

/- English proof (translation)
The claim follows from `rmStep_contDiff.continuous`.
-/
lemma rmStep_continuous : Continuous rmStep := rmStep_contDiff.continuous

/- English proof (translation)
Introduce `a b h`. Use `Real.smoothTransition.monotone (show a + 1 / 2 ≤ b + 1 / 2 by linarith)` as an intermediate fact. Unfold `rmStep`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma rmStep_monotone : Monotone rmStep := by
  intro a b h
  have := Real.smoothTransition.monotone (show a + 1 / 2 ≤ b + 1 / 2 by linarith)
  unfold rmStep
  linarith

/- English proof (translation)
Unfold `rmStep`. Rewrite using `[Real.smoothTransition.one_of_one_le (by linarith)]`. Evaluate the numerical expressions.
-/
lemma rmStep_of_le (t : ℝ) (h : 1 / 2 ≤ t) : rmStep t = 1 := by
  unfold rmStep
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  norm_num

/- English proof (translation)
Unfold `rmStep`. Rewrite using `[Real.smoothTransition.zero_of_nonpos (by linarith)]`. Evaluate the numerical expressions.
-/
lemma rmStep_of_ge (t : ℝ) (h : t ≤ -1 / 2) : rmStep t = -1 := by
  unfold rmStep
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num

/- English proof (translation)
Establish `h0` using `Real.smoothTransition.nonneg (t + 1 / 2)`. Establish `h1` using `Real.smoothTransition.le_one (t + 1 / 2)`. Unfold `rmStep`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`.
-/
lemma abs_rmStep_le (t : ℝ) : |rmStep t| ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (t + 1 / 2)
  have h1 := Real.smoothTransition.le_one (t + 1 / 2)
  unfold rmStep
  rw [abs_le]
  constructor <;> linarith

def rmPrim (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, rmStep s

/- English proof (translation)
The claim follows from `(rmStep_continuous.integral_hasStrictDerivAt 0 t).hasDerivAt`.
-/
lemma rmPrim_hasDerivAt (t : ℝ) : HasDerivAt rmPrim (rmStep t) t :=
  (rmStep_continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

def rmRho0 (t : ℝ) : ℝ := (rmPrim t + rmPrim (-t)) / 2

def rmRho (t : ℝ) : ℝ := rmRho0 t + (1 / 2 - rmRho0 (1 / 2))

def rmRho' (t : ℝ) : ℝ := (rmStep t - rmStep (-t)) / 2

/- English proof (translation)
Establish `h1` using `rmPrim_hasDerivAt t`. Establish `h2 : HasDerivAt (fun s => rmPrim (-s)) (-rmStep (-t)) t`. Use `(rmPrim_hasDerivAt (-t)).comp t (hasDerivAt_neg t)` as an intermediate fact. Rewrite `this` using `[mul_neg_one]`. Conclude with `this`.

Establish `h3` using `((h1.add h2).div_const 2).add_const (1 / 2 - rmRho0 (1 / 2))`. Establish `h4 : rmRho' t = (rmStep t + -rmStep (-t)) / 2`. Unfold `rmRho'`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`.

Conclude with `h3`.
-/
lemma rmRho_hasDerivAt (t : ℝ) : HasDerivAt rmRho (rmRho' t) t := by
  have h1 := rmPrim_hasDerivAt t
  have h2 : HasDerivAt (fun s => rmPrim (-s)) (-rmStep (-t)) t := by
    have := (rmPrim_hasDerivAt (-t)).comp t (hasDerivAt_neg t)
    rw [mul_neg_one] at this
    exact this
  have h3 := ((h1.add h2).div_const 2).add_const (1 / 2 - rmRho0 (1 / 2))
  have h4 : rmRho' t = (rmStep t + -rmStep (-t)) / 2 := by
    unfold rmRho'
    ring
  rw [h4]
  exact h3

/- English proof (translation)
The claim follows from `funext fun t => (rmRho_hasDerivAt t).deriv`.
-/
lemma rmRho_deriv : deriv rmRho = rmRho' := funext fun t => (rmRho_hasDerivAt t).deriv

/- English proof (translation)
Unfold `rmRho'`. Conclude with `(rmStep_contDiff.sub (rmStep_contDiff.comp contDiff_neg)).div_const 2`.
-/
lemma rmRho'_contDiff : ContDiff ℝ ∞ rmRho' := by
  unfold rmRho'
  exact (rmStep_contDiff.sub (rmStep_contDiff.comp contDiff_neg)).div_const 2

/- English proof (translation)
Rewrite using `[contDiff_infty_iff_deriv, rmRho_deriv]`. Conclude with `⟨fun t => (rmRho_hasDerivAt t).differentiableAt, rmRho'_contDiff⟩`.
-/
lemma rmRho_contDiff : ContDiff ℝ ∞ rmRho := by
  rw [contDiff_infty_iff_deriv, rmRho_deriv]
  exact ⟨fun t => (rmRho_hasDerivAt t).differentiableAt, rmRho'_contDiff⟩

/- English proof (translation)
Establish `h1` using `abs_le.mp (abs_rmStep_le t)`. Establish `h2` using `abs_le.mp (abs_rmStep_le (-t))`. Unfold `rmRho'`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]`.
-/
lemma abs_rmRho'_le (t : ℝ) : |rmRho' t| ≤ 1 := by
  have h1 := abs_le.mp (abs_rmStep_le t)
  have h2 := abs_le.mp (abs_rmStep_le (-t))
  unfold rmRho'
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/- English proof (translation)
Introduce `a b h`. Establish `h1` using `rmStep_monotone h`. Establish `h2` using `rmStep_monotone (show -b ≤ -a by linarith)`. Unfold `rmRho'`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma rmRho'_monotone : Monotone rmRho' := by
  intro a b h
  have h1 := rmStep_monotone h
  have h2 := rmStep_monotone (show -b ≤ -a by linarith)
  unfold rmRho'
  linarith

/- English proof (translation)
Unfold `rmRho rmRho0`. Rewrite using `[neg_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma rmRho_even (t : ℝ) : rmRho (-t) = rmRho t := by
  unfold rmRho rmRho0
  rw [neg_neg]
  ring

/- English proof (translation)
Establish `hg : ∀ x ∈ Set.Icc (1 / 2 : ℝ) t, rmRho x - x = rmRho (1 / 2) - 1 / 2`. Use `constant_of_has_deriv_right_zero (f := fun x => rmRho x - x) ?_ ?_` and prove the remaining obligations. Conclude with `(rmRho_contDiff.continuous.sub continuous_id).continuousOn`. Introduce `x hx`. Establish `hx1 : 1 / 2 ≤ x` using `hx.1`.

Establish `hd` using `(rmRho_hasDerivAt x).sub (hasDerivAt_id x)`. Establish `h0 : rmRho' x - 1 = 0`. Unfold `rmRho'`. Rewrite using `[rmStep_of_le x hx1, rmStep_of_ge (-x) (by linarith)]`. Evaluate the numerical expressions.

Rewrite `hd` using `[h0]`. Conclude with `hd.hasDerivWithinAt`. Establish `h12 : rmRho (1 / 2) = 1 / 2`. Unfold `rmRho`. Expand and normalize the polynomial expressions, which then agree.

Use `hg t ⟨h, le_rfl⟩` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma rmRho_of_le (t : ℝ) (h : 1 / 2 ≤ t) : rmRho t = t := by
  have hg : ∀ x ∈ Set.Icc (1 / 2 : ℝ) t, rmRho x - x = rmRho (1 / 2) - 1 / 2 := by
    refine constant_of_has_deriv_right_zero (f := fun x => rmRho x - x) ?_ ?_
    · exact (rmRho_contDiff.continuous.sub continuous_id).continuousOn
    · intro x hx
      have hx1 : 1 / 2 ≤ x := hx.1
      have hd := (rmRho_hasDerivAt x).sub (hasDerivAt_id x)
      have h0 : rmRho' x - 1 = 0 := by
        unfold rmRho'
        rw [rmStep_of_le x hx1, rmStep_of_ge (-x) (by linarith)]
        norm_num
      rw [h0] at hd
      exact hd.hasDerivWithinAt
  have h12 : rmRho (1 / 2) = 1 / 2 := by
    unfold rmRho
    ring
  have := hg t ⟨h, le_rfl⟩
  linarith

/- English proof (translation)
Break down `le_or_gt 0 t with h0 | h0` into its components or cases. Rewrite `h`, the goal using `[abs_of_nonneg h0]`. Conclude with `rmRho_of_le t h`. Rewrite `h`, the goal using `[abs_of_neg h0]`. Rewrite using `[← rmRho_even]`.

Conclude with `rmRho_of_le (-t) h`.
-/
lemma rmRho_of_abs (t : ℝ) (h : 1 / 2 ≤ |t|) : rmRho t = |t| := by
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    exact rmRho_of_le t h
  · rw [abs_of_neg h0] at h ⊢
    rw [← rmRho_even]
    exact rmRho_of_le (-t) h

/- English proof (translation)
Establish `hL : LipschitzWith 1 rmRho`. Use `lipschitzWith_of_nnnorm_deriv_le (fun x => (rmRho_hasDerivAt x).differentiableAt) fun x => ?_` and prove the remaining obligations. Rewrite using `[rmRho_deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]`. Conclude with `abs_rmRho'_le x`. Use `hL.dist_le_mul a b` as an intermediate fact.

Simplify `this` using `[Real.dist_eq]`.
-/
lemma rmRho_lip (a b : ℝ) : |rmRho a - rmRho b| ≤ |a - b| := by
  have hL : LipschitzWith 1 rmRho := by
    refine lipschitzWith_of_nnnorm_deriv_le (fun x => (rmRho_hasDerivAt x).differentiableAt) fun x => ?_
    rw [rmRho_deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    exact abs_rmRho'_le x
  have := hL.dist_le_mul a b
  simpa [Real.dist_eq] using this

/- English proof (translation)
Establish `h12 : rmRho (1 / 2) = 1 / 2`. Unfold `rmRho`. Expand and normalize the polynomial expressions, which then agree. Establish `hanti : Antitone (fun x => rmRho x - x)`. Establish `hd : ∀ x, HasDerivAt (fun x => rmRho x - x) (rmRho' x - 1) x` using `fun x => (rmRho_hasDerivAt x).sub (hasDerivAt_id x)`.

Use `antitone_of_deriv_nonpos (fun x => (hd x).differentiableAt) fun x => ?_` and prove the remaining obligations. Rewrite using `[(hd x).deriv]`. Use `(abs_le.mp (abs_rmRho'_le x)).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hge : ∀ s : ℝ, s ≤ rmRho s`.

Introduce `s`. Break down `le_or_gt s (1 / 2) with hs | hs` into its components or cases. Use `hanti hs` as an intermediate fact. Simplify using `only at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[rmRho_of_le s hs.le]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[abs_le]`. Prove the components needed by the constructor for the conclusion. Use `hge (-t)` as an intermediate fact.

Rewrite `this` using `[rmRho_even]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hge t`. Establish `hl` using `rmRho_lip t (1 / 2)`. Establish `hA : |t - 1 / 2| ≤ |t| + 1 / 2` using `abs_le.mpr ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩`.

Use `le_abs_self (rmRho t - rmRho (1 / 2))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma rmRho_bounds (t : ℝ) : |t| ≤ rmRho t ∧ rmRho t ≤ |t| + 1 := by
  have h12 : rmRho (1 / 2) = 1 / 2 := by
    unfold rmRho
    ring
  have hanti : Antitone (fun x => rmRho x - x) := by
    have hd : ∀ x, HasDerivAt (fun x => rmRho x - x) (rmRho' x - 1) x :=
      fun x => (rmRho_hasDerivAt x).sub (hasDerivAt_id x)
    refine antitone_of_deriv_nonpos (fun x => (hd x).differentiableAt) fun x => ?_
    rw [(hd x).deriv]
    have := (abs_le.mp (abs_rmRho'_le x)).2
    linarith
  have hge : ∀ s : ℝ, s ≤ rmRho s := by
    intro s
    rcases le_or_gt s (1 / 2) with hs | hs
    · have := hanti hs
      simp only at this
      linarith
    · rw [rmRho_of_le s hs.le]
  constructor
  · rw [abs_le]
    constructor
    · have := hge (-t)
      rw [rmRho_even] at this
      linarith
    · exact hge t
  · have hl := rmRho_lip t (1 / 2)
    have hA : |t - 1 / 2| ≤ |t| + 1 / 2 := abs_le.mpr ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have := le_abs_self (rmRho t - rmRho (1 / 2))
    linarith

variable {n : ℕ}

/- English proof (translation)
Use `filter_upwards [hF.eventually (by simp)] with x hx`. Establish `hd : HasFDerivAt (fun x => (F x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ F x)) x` using `Complex.ofRealCLM.hasFDerivAt.comp x (hx.differentiableAt (by norm_num)).hasFDerivAt`. Unfold `wdb`. Rewrite using `[hd.fderiv]`. Simplify using the standard rewrite rules.
-/
lemma rm_wdb_ofReal_eventually (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (k : Fin n) :
    wdb n k (fun x => (F x : ℂ)) =ᶠ[𝓝 y] fun x =>
      (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2 := by
  filter_upwards [hF.eventually (by simp)] with x hx
  have hd : HasFDerivAt (fun x => (F x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ F x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hx.differentiableAt (by norm_num)).hasFDerivAt
  unfold wdb
  rw [hd.fderiv]
  simp

/- English proof (translation)
Establish `h1 : ContDiffAt ℝ 1 (fderiv ℝ F) y` using `hF.fderiv_right (by norm_num)`. Establish `h2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) y) y` using `(h1.differentiableAt (by norm_num)).hasFDerivAt`. Establish `h3 : HasFDerivAt (fun x => fderiv ℝ F x w) ((fderiv ℝ (fderiv ℝ F) y).flip w) y`. Use `h2.clm_apply (hasFDerivAt_const w y)` as an intermediate fact. Rewrite `this` using `[ContinuousLinearMap.comp_zero, zero_add]`.

Conclude with `this`. Conclude with `Complex.ofRealCLM.hasFDerivAt.comp y h3`.
-/
lemma rm_hasFDerivAt_fderiv_apply_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y)
    (w : V n) :
    HasFDerivAt (fun x => ((fderiv ℝ F x w : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ F) y).flip w)) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) y := hF.fderiv_right (by norm_num)
  have h2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) y) y :=
    (h1.differentiableAt (by norm_num)).hasFDerivAt
  have h3 : HasFDerivAt (fun x => fderiv ℝ F x w) ((fderiv ℝ (fderiv ℝ F) y).flip w) y := by
    have := h2.clm_apply (hasFDerivAt_const w y)
    rw [ContinuousLinearMap.comp_zero, zero_add] at this
    exact this
  exact Complex.ofRealCLM.hasFDerivAt.comp y h3

/- English proof (translation)
Establish `hS` using `(rm_hasFDerivAt_fderiv_apply_ofReal F y hF (bas n k)).add ((rm_hasFDerivAt_fderiv_apply_ofReal F y hF (Complex.I • bas n k)).const_mul Complex.I)`. Establish `hG` using `HasFDerivAt.const_mul (𝔸 := ℂ) hS ((2 : ℂ)⁻¹)`. Establish `hfd` using `Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (rm_wdb_ofReal_eventually F y hF k)`. Establish `hfun : (fun x => (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) + Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2) = fun x => (2 : ℂ)⁻¹ * (((fun x => ((fderiv ℝ F x (bas n k) : ℝ) : ℂ)) + fun y => Complex.I * ((fderiv ℝ F y (Complex.I • bas n k) : ℝ) : ℂ)) x)`. Use function extensionality and compare the values at `x`.

Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Unfold `wd`. Rewrite using `[hfd, hfun, hG.fderiv]`. Simplify using the standard rewrite rules.

Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma rm_wd_wdb_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (j k : Fin n) :
    wd n j (wdb n k (fun x => (F x : ℂ))) y =
      (((fderiv ℝ (fderiv ℝ F) y (bas n j) (bas n k) : ℝ) : ℂ)
        + Complex.I * ((fderiv ℝ (fderiv ℝ F) y (bas n j) (Complex.I • bas n k) : ℝ) : ℂ)
        - Complex.I * ((fderiv ℝ (fderiv ℝ F) y (Complex.I • bas n j) (bas n k) : ℝ) : ℂ)
        + ((fderiv ℝ (fderiv ℝ F) y (Complex.I • bas n j) (Complex.I • bas n k) : ℝ) : ℂ)) / 4 := by
  have hS := (rm_hasFDerivAt_fderiv_apply_ofReal F y hF (bas n k)).add
    ((rm_hasFDerivAt_fderiv_apply_ofReal F y hF (Complex.I • bas n k)).const_mul Complex.I)
  have hG := HasFDerivAt.const_mul (𝔸 := ℂ) hS ((2 : ℂ)⁻¹)
  have hfd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (rm_wdb_ofReal_eventually F y hF k)
  have hfun : (fun x => (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) +
      Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2) =
      fun x => (2 : ℂ)⁻¹ * (((fun x => ((fderiv ℝ F x (bas n k) : ℝ) : ℂ)) +
        fun y => Complex.I * ((fderiv ℝ F y (Complex.I • bas n k) : ℝ) : ℂ)) x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  unfold wd
  rw [hfd, hfun, hG.fderiv]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

def rmVec (ξ : Fin n → ℂ) : V n := ∑ j, ξ j • bas n j

/- English proof (translation)
Use `conv_lhs => rw [← Complex.re_add_im z]`. Rewrite using `[add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]`.
-/
lemma rm_cplx_smul_eq (z : ℂ) (x : V n) : z • x = z.re • x + z.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

/- English proof (translation)
Rewrite using `[rm_cplx_smul_eq z a, rm_cplx_smul_eq w b]`. Simplify using `only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma rm_bil_expand (B : V n →L[ℝ] V n →L[ℝ] ℝ) (z w : ℂ) (a b : V n) :
    B (z • a) (w • b) = z.re * w.re * B a b + z.re * w.im * B a (Complex.I • b)
      + z.im * w.re * B (Complex.I • a) b + z.im * w.im * B (Complex.I • a) (Complex.I • b) := by
  rw [rm_cplx_smul_eq z a, rm_cplx_smul_eq w b]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Simplify using `only [map_sum, ContinuousLinearMap.sum_apply]`. Conclude with `Finset.sum_comm`.
-/
lemma rm_bil_sum (B : V n →L[ℝ] V n →L[ℝ] ℝ) (c : Fin n → ℂ) :
    B (∑ j, c j • bas n j) (∑ k, c k • bas n k) = ∑ j, ∑ k, B (c j • bas n j) (c k • bas n k) := by
  simp only [map_sum, ContinuousLinearMap.sum_apply]
  exact Finset.sum_comm

/- English proof (translation)
Unfold `rmVec`. Rewrite using `[Finset.smul_sum]`. Repeatedly rewrite using `[smul_smul]`.
-/
lemma rm_I_smul_vec (ξ : Fin n → ℂ) : Complex.I • rmVec ξ = ∑ j, (Complex.I * ξ j) • bas n j := by
  unfold rmVec
  rw [Finset.smul_sum]
  simp_rw [smul_smul]

/- English proof (translation)
Rewrite using `[rm_I_smul_vec]`. Unfold `rmVec`. Rewrite using `[rm_bil_sum, rm_bil_sum, ← Finset.sum_add_distrib]`. Unfold `leviV`. Rewrite using `[Complex.re_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib, Complex.re_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[rm_wd_wdb_ofReal F y hF j k, rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (ξ j) (ξ k), rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (Complex.I * ξ j) (Complex.I * ξ k)]`. Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]`.

Simplify using `[Complex.mul_re, Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rm_levi_re_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (ξ : Fin n → ℂ) :
    4 * (leviV n (fun x => (F x : ℂ)) y ξ).re =
      fderiv ℝ (fderiv ℝ F) y (rmVec ξ) (rmVec ξ) +
        fderiv ℝ (fderiv ℝ F) y (Complex.I • rmVec ξ) (Complex.I • rmVec ξ) := by
  rw [rm_I_smul_vec]
  unfold rmVec
  rw [rm_bil_sum, rm_bil_sum, ← Finset.sum_add_distrib]
  unfold leviV
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rm_wd_wdb_ofReal F y hF j k, rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (ξ j) (ξ k),
    rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (Complex.I * ξ j) (Complex.I * ξ k)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
