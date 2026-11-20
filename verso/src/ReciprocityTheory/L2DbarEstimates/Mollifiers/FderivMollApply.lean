import ReciprocityTheory.L2DbarEstimates.Mollifiers.HasCompactSupport

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

/- English proof (translation)
Establish `hcs : HasCompactSupport K.toFun` using `HasCompactSupport.intro (isCompact_closedBall (0 : E) K.r) fun y hy => by`. Assume the negation of the conclusion as `h`. Conclude with `hy (ball_subset_closedBall (K.support_subset h))`. Establish `hd` using `hcs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (K.smooth.of_le (by simp)) hu x`. Establish `hmoll : moll K u = K.toFun ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u` using `rfl`.

Rewrite using `[hmoll, hd.fderiv]`. Establish `hex` using `(hcs.fderiv ℝ).convolutionExists_left ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E) (K.smooth.continuous_fderiv (by simp)) hu x`. Rewrite using `[convolution_def, ContinuousLinearMap.integral_apply hex]`. Rewrite using `[← integral_sub_left_eq_self _ μ x]`. Use `congr 1`.

Use extensionality with `y`. Rewrite using `[sub_sub_cancel]`. Both sides reduce to the same expression.
-/
theorem fderiv_moll_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) {u : E → ℂ} (hu : LocallyIntegrable u μ)
    (x a : E) :
    fderiv ℝ (moll K u) x a = ∫ y, (fderiv ℝ K.toFun (x - y) a) • u y ∂μ := by
  have hcs : HasCompactSupport K.toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) K.r) fun y hy => by
      by_contra h
      exact hy (ball_subset_closedBall (K.support_subset h))
  have hd := hcs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (K.smooth.of_le (by simp)) hu x
  have hmoll : moll K u = K.toFun ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u := rfl
  rw [hmoll, hd.fderiv]
  have hex := (hcs.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E) (K.smooth.continuous_fderiv (by simp)) hu x
  rw [convolution_def, ContinuousLinearMap.integral_apply hex]
  rw [← integral_sub_left_eq_self _ μ x]
  congr 1
  ext y
  rw [sub_sub_cancel]
  rfl

/- English proof (translation)
Introduce `m c v g w hw K`. Use function extensionality and compare the values at `x`. Establish `hd : ∀ k, fderiv ℝ (moll K (g k)) x (v k) = ∫ y, (fderiv ℝ K.toFun (x - y) (v k)) • g k y ∂μ` using `fun k => fderiv_moll_apply E μ K (hw.1 k) x (v k)`. Use `set φ : E → ℂ := fun y => ((K.toFun (x - y) : ℝ) : ℂ) with hφdef`. Establish `hφs : ContDiff ℝ ∞ φ` using `Complex.ofRealCLM.contDiff.comp (K.smooth.comp (contDiff_const.sub contDiff_id))`.

Establish `hφc : HasCompactSupport φ` using `HasCompactSupport.intro (isCompact_closedBall x K.r) fun y hy => by`. Simplify using `only [hφdef, Complex.ofReal_eq_zero]`. Assume the negation of the conclusion as `h`. Apply `hy` to reduce the goal to its premises. Establish `h'` using `K.support_subset h`.

Rewrite `h'` using `[mem_ball_zero_iff]`. Rewrite using `[mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]`. Conclude with `h'.le`. Establish `hw3` using `hw.2.2 φ hφs hφc`. Establish `hdφ : ∀ y a, fderiv ℝ φ y a = -((fderiv ℝ K.toFun (x - y) a : ℝ) : ℂ)`.

Introduce `y a`. Establish `h1 : HasFDerivAt (fun y : E => x - y) (-ContinuousLinearMap.id ℝ E) y` using `(hasFDerivAt_id y).const_sub x`. Establish `h2` using `((K.smooth.differentiable (by simp)) (x - y)).hasFDerivAt.comp y h1`. Establish `h3` using `Complex.ofRealCLM.hasFDerivAt.comp y h2`. Rewrite using `[(show HasFDerivAt φ _ y from h3).fderiv]`.

Simplify using the standard rewrite rules. Establish `hm : moll K w x = ∫ y, w y * φ y ∂μ` using `by show ∫ t, K.toFun t • w (x - t) ∂μ = _`. Rewrite using `[← integral_sub_left_eq_self (fun t => K.toFun t • w (x - t)) μ x]`. Use `congr 1`. Use extensionality with `y`.

Simplify using `only [hφdef, sub_sub_cancel, Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Dop, hd]`. Rewrite using `[hm, hw3, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_neg, ← integral_neg]`. Use `congr 2`. Use extensionality with `y`. Rewrite using `[hdφ, Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem moll_weakComm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : WeakCommSt E μ := by
  intro m c v g w hw K
  funext x
  have hd : ∀ k, fderiv ℝ (moll K (g k)) x (v k) =
      ∫ y, (fderiv ℝ K.toFun (x - y) (v k)) • g k y ∂μ :=
    fun k => fderiv_moll_apply E μ K (hw.1 k) x (v k)
  set φ : E → ℂ := fun y => ((K.toFun (x - y) : ℝ) : ℂ) with hφdef
  have hφs : ContDiff ℝ ∞ φ :=
    Complex.ofRealCLM.contDiff.comp (K.smooth.comp (contDiff_const.sub contDiff_id))
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall x K.r) fun y hy => by
      simp only [hφdef, Complex.ofReal_eq_zero]
      by_contra h
      apply hy
      have h' := K.support_subset h
      rw [mem_ball_zero_iff] at h'
      rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
      exact h'.le
  have hw3 := hw.2.2 φ hφs hφc
  have hdφ : ∀ y a, fderiv ℝ φ y a = -((fderiv ℝ K.toFun (x - y) a : ℝ) : ℂ) := by
    intro y a
    have h1 : HasFDerivAt (fun y : E => x - y) (-ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 := ((K.smooth.differentiable (by simp)) (x - y)).hasFDerivAt.comp y h1
    have h3 := Complex.ofRealCLM.hasFDerivAt.comp y h2
    rw [(show HasFDerivAt φ _ y from h3).fderiv]
    simp
  have hm : moll K w x = ∫ y, w y * φ y ∂μ := by
    show ∫ t, K.toFun t • w (x - t) ∂μ = _
    rw [← integral_sub_left_eq_self (fun t => K.toFun t • w (x - t)) μ x]
    congr 1
    ext y
    simp only [hφdef, sub_sub_cancel, Complex.real_smul]
    ring
  simp only [Dop, hd]
  rw [hm, hw3, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_neg, ← integral_neg]
  congr 2
  ext y
  rw [hdφ, Complex.real_smul]
  ring

/- English proof (translation)
Introduce `m c v g hg`. Establish `hgd : ∀ k, Differentiable ℝ (g k)` using `fun k => (hg k).differentiable (by simp)`. Establish `hgc : ∀ k, Continuous (fun x => fderiv ℝ (g k) x (v k))` using `fun k => ((hg k).continuous_fderiv (by simp)).clm_apply continuous_const`. Use `⟨fun k => (hg k).continuous.locallyIntegrable, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : Continuous (Dop c v g)`.

Unfold `Dop`. Conclude with `continuous_finset_sum _ fun k _ => continuous_const.mul (hgc k)`. Conclude with `hc.locallyIntegrable`. Introduce `φ hφ hφc`. Establish `hφd : Differentiable ℝ φ` using `hφ.differentiable (by simp)`.

Establish `hφ' : ∀ k, Continuous (fun x => fderiv ℝ φ x (v k))` using `fun k => (hφ.continuous_fderiv (by simp)).clm_apply continuous_const`. Establish `hφ'c : ∀ k, HasCompactSupport (fun x => fderiv ℝ φ x (v k))` using `fun k => (hφc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℂ => L (v k)) (by simp)`. Establish `int1 : ∀ k, Integrable (fun x => fderiv ℝ (g k) x (v k) * φ x) μ` using `fun k => ((hgc k).mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left`. Establish `int2 : ∀ k, Integrable (fun x => g k x * fderiv ℝ φ x (v k)) μ` using `fun k => ((hg k).continuous.mul (hφ' k)).integrable_of_hasCompactSupport (hφ'c k).mul_left`. Establish `int3 : ∀ k, Integrable (fun x => g k x * φ x) μ` using `fun k => ((hg k).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left`.

Establish `hibp : ∀ k, ∫ x, g k x * fderiv ℝ φ x (v k) ∂μ = -∫ x, fderiv ℝ (g k) x (v k) * φ x ∂μ` using `fun k => integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (int1 k) (int2 k) (int3 k) (fun x _ => hgd k x) (fun x _ => hφd x)`. Establish `hsum : ∫ x, Dop c v g x * φ x ∂μ = ∑ k, c k * ∫ x, fderiv ℝ (g k) x (v k) * φ x ∂μ`. Simplify using `only [Dop, Finset.sum_mul]`. Rewrite using `[integral_finset_sum _ fun k _ => by simpa [mul_assoc] using (int1 k).const_mul (c k)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use extensionality with `x`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hibp k, mul_neg, neg_neg]`.
-/
theorem smooth_isWeakD (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : SmoothWeakSt E μ := by
  intro m c v g hg
  have hgd : ∀ k, Differentiable ℝ (g k) := fun k => (hg k).differentiable (by simp)
  have hgc : ∀ k, Continuous (fun x => fderiv ℝ (g k) x (v k)) := fun k =>
    ((hg k).continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨fun k => (hg k).continuous.locallyIntegrable, ?_, ?_⟩
  · have hc : Continuous (Dop c v g) := by
      unfold Dop
      exact continuous_finset_sum _ fun k _ => continuous_const.mul (hgc k)
    exact hc.locallyIntegrable
  · intro φ hφ hφc
    have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hφ' : ∀ k, Continuous (fun x => fderiv ℝ φ x (v k)) := fun k =>
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hφ'c : ∀ k, HasCompactSupport (fun x => fderiv ℝ φ x (v k)) := fun k =>
      (hφc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℂ => L (v k)) (by simp)
    have int1 : ∀ k, Integrable (fun x => fderiv ℝ (g k) x (v k) * φ x) μ := fun k =>
      ((hgc k).mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have int2 : ∀ k, Integrable (fun x => g k x * fderiv ℝ φ x (v k)) μ := fun k =>
      ((hg k).continuous.mul (hφ' k)).integrable_of_hasCompactSupport (hφ'c k).mul_left
    have int3 : ∀ k, Integrable (fun x => g k x * φ x) μ := fun k =>
      ((hg k).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have hibp : ∀ k, ∫ x, g k x * fderiv ℝ φ x (v k) ∂μ =
        -∫ x, fderiv ℝ (g k) x (v k) * φ x ∂μ := fun k =>
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (int1 k) (int2 k) (int3 k)
        (fun x _ => hgd k x) (fun x _ => hφd x)
    have hsum : ∫ x, Dop c v g x * φ x ∂μ =
        ∑ k, c k * ∫ x, fderiv ℝ (g k) x (v k) * φ x ∂μ := by
      simp only [Dop, Finset.sum_mul]
      rw [integral_finset_sum _ fun k _ => by simpa [mul_assoc] using (int1 k).const_mul (c k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← integral_const_mul]
      congr 1
      ext x
      ring
    rw [hsum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hibp k, mul_neg, neg_neg]

end ReciprocityTheory.L2DbarEstimates.B
