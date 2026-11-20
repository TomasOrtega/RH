import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralBumpProfOnePos

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

noncomputable def smulFlip : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip

/- English proof (translation)
Simplify using `only [smulFlip, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, Complex.real_smul]`.
-/
theorem smulFlip_apply (a : ℂ) (r : ℝ) : smulFlip a r = (r : ℂ) * a := by
  simp only [smulFlip, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mollify, convolution_def, smulFlip_apply]`.
-/
theorem mollify_eq_convolution_smulFlip (n : ℕ) (t : ℝ) (u : V n → ℂ) :
    mollify n t u = convolution u (moll n t) smulFlip volume := by
  ext x
  simp only [mollify, convolution_def, smulFlip_apply]

/- English proof (translation)
The claim follows from `(moll_contDiff n t).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))`.
-/
theorem moll_contDiff_one (n : ℕ) (t : ℝ) : ContDiff ℝ 1 (moll n t) := (moll_contDiff n t).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))

/- English proof (translation)
Apply `image_eq_zero_of_notMem_tsupport` to reduce the goal to its premises. Introduce `h`. Apply `hy` to reduce the goal to its premises. Use `moll_tsupport n ht h` as an intermediate fact. Rewrite `this` using `[mem_closedBall, dist_zero_right]`.

Rewrite using `[mem_closedBall, dist_eq_norm, norm_sub_rev]`. Conclude with `this`.
-/
theorem moll_sub_eq_zero {n : ℕ} {t : ℝ} (ht : 0 < t) {x y : V n}
    (hy : y ∉ closedBall x (t / 2)) : moll n t (x - y) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  apply hy
  have := moll_tsupport n ht h
  rw [mem_closedBall, dist_zero_right] at this
  rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
  exact this

/- English proof (translation)
Establish `hz : ∀ y ∉ closedBall x (t / 2), ((moll n t (x - y) : ℝ) : ℂ) = 0` using `fun y hy => by`. Rewrite using `[moll_sub_eq_zero ht hy, Complex.ofReal_zero]`. Use `⟨?_, HasCompactSupport.intro (isCompact_closedBall x (t / 2)) hz, ?_⟩` and prove the remaining obligations. Conclude with `Complex.ofRealCLM.contDiff.comp ((moll_contDiff n t).comp (contDiff_const.sub contDiff_id))`. Conclude with `(closure_minimal (Function.support_subset_iff'.2 hz) isClosed_closedBall).trans ((closedBall_subset_closedBall (by linarith)).trans hx)`.
-/
theorem isTest_moll_sub {n : ℕ} {Ω : Set (V n)} {t : ℝ} {x : V n} (ht : 0 < t)
    (hx : closedBall x t ⊆ Ω) : IsTest Ω (fun y => ((moll n t (x - y) : ℝ) : ℂ)) := by
  have hz : ∀ y ∉ closedBall x (t / 2), ((moll n t (x - y) : ℝ) : ℂ) = 0 := fun y hy => by
    rw [moll_sub_eq_zero ht hy, Complex.ofReal_zero]
  refine ⟨?_, HasCompactSupport.intro (isCompact_closedBall x (t / 2)) hz, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((moll_contDiff n t).comp (contDiff_const.sub contDiff_id))
  · exact (closure_minimal (Function.support_subset_iff'.2 hz) isClosed_closedBall).trans
      ((closedBall_subset_closedBall (by linarith)).trans hx)

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ (moll n t) (x - y)` using `(moll_contDiff_one n t).differentiable one_ne_zero (x - y)`. Establish `h1 : HasFDerivAt (fun y : V n => x - y) (-ContinuousLinearMap.id ℝ (V n)) y` using `(hasFDerivAt_id y).const_sub x`. Establish `h2` using `Complex.ofRealCLM.hasFDerivAt.comp y (hd.hasFDerivAt.comp y h1)`. Rewrite using `[show (fun y => ((moll n t (x - y) : ℝ) : ℂ)) = Complex.ofRealCLM ∘ (moll n t ∘ fun y => x - y) from rfl, h2.fderiv]`. Simplify using the standard rewrite rules.
-/
theorem fderiv_moll_sub {n : ℕ} {t : ℝ} (x y w : V n) :
    fderiv ℝ (fun y => ((moll n t (x - y) : ℝ) : ℂ)) y w
      = -((fderiv ℝ (moll n t) (x - y) w : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ (moll n t) (x - y) :=
    (moll_contDiff_one n t).differentiable one_ne_zero (x - y)
  have h1 : HasFDerivAt (fun y : V n => x - y) (-ContinuousLinearMap.id ℝ (V n)) y :=
    (hasFDerivAt_id y).const_sub x
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp y (hd.hasFDerivAt.comp y h1)
  rw [show (fun y => ((moll n t (x - y) : ℝ) : ℂ)) =
    Complex.ofRealCLM ∘ (moll n t ∘ fun y => x - y) from rfl, h2.fderiv]
  simp

/- English proof (translation)
Establish `hsmul : ∀ (c : ℂ) (v : V n), fderiv ℝ f x (c • v) = c * fderiv ℝ f x v`. Introduce `c v`. Use `conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]`. Rewrite using `[map_add, map_smul, map_smul, h, Complex.real_smul, Complex.real_smul]`. Use `conv_rhs => rw [← Complex.re_add_im c]`.

Expand and normalize the polynomial expressions, which then agree. Set `g' : V n →L[ℂ] ℂ` to `⟨⟨⟨fderiv ℝ f x, (fderiv ℝ f x).map_add⟩, fun c v => by simpa using hsmul c v⟩, (fderiv ℝ f x).continuous⟩`. Conclude with `(differentiableAt_iff_restrictScalars ℝ hf).2 ⟨g', ContinuousLinearMap.ext fun _ => rfl⟩`.
-/
theorem differentiableAt_of_fderiv_I {n : ℕ} {f : V n → ℂ} {x : V n}
    (hf : DifferentiableAt ℝ f x)
    (h : ∀ v, fderiv ℝ f x (I • v) = I * fderiv ℝ f x v) : DifferentiableAt ℂ f x := by
  have hsmul : ∀ (c : ℂ) (v : V n), fderiv ℝ f x (c • v) = c * fderiv ℝ f x v := by
    intro c v
    conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    rw [map_add, map_smul, map_smul, h, Complex.real_smul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  let g' : V n →L[ℂ] ℂ :=
    ⟨⟨⟨fderiv ℝ f x, (fderiv ℝ f x).map_add⟩, fun c v => by simpa using hsmul c v⟩,
      (fderiv ℝ f x).continuous⟩
  exact (differentiableAt_iff_restrictScalars ℝ hf).2 ⟨g', ContinuousLinearMap.ext fun _ => rfl⟩

/- English proof (translation)
Establish `hcs` using `moll_hasCompactSupport n ht`. Establish `hc1` using `moll_contDiff_one n t`. Establish `hli : LocallyIntegrable u volume` using `hu.locallyIntegrable`. Establish `hD` using `hcs.hasFDerivAt_convolution_right (L := smulFlip) hli hc1 x`. Establish `hcont : ∀ v, Continuous (fun a => fderiv ℝ (moll n t) a v)` using `fun v => (hc1.continuous_fderiv one_ne_zero).clm_apply continuous_const`.

Establish `hint : ∀ v, Integrable (fun s => ((fderiv ℝ (moll n t) (x - s) v : ℝ) : ℂ) * u s)`. Introduce `v`. Use `(((hcs.fderiv_apply (𝕜 := ℝ) v).convolutionExists_right smulFlip hli (hcont v)) x)` as an intermediate fact. Simplify `this` using `[ConvolutionExistsAt, smulFlip_apply]`. Rewrite using `[mollify_eq_convolution_smulFlip]`.

Apply `differentiableAt_of_fderiv_I hD.differentiableAt` to reduce the goal to its premises. Introduce `w`. Rewrite using `[hD.fderiv, convolution_precompR_apply smulFlip hli (hcs.fderiv (𝕜 := ℝ)) (hc1.continuous_fderiv one_ne_zero), convolution_precompR_apply smulFlip hli (hcs.fderiv (𝕜 := ℝ)) (hc1.continuous_fderiv one_ne_zero)]`. Simplify using `only [convolution_def, smulFlip_apply]`. Establish `h0` using `hw.2 (fun y => ((moll n t (x - y) : ℝ) : ℂ)) (isTest_moll_sub ht hx) w`.

Rewrite `h0` using `[setIntegral_eq_integral_of_forall_compl_eq_zero]`. Simplify using `only [dbarDir, fderiv_moll_sub] at h0`. Establish `hsplit : ∫ z, u z * (-((fderiv ℝ (moll n t) (x - z) (I • w) : ℝ) : ℂ) - I * -((fderiv ℝ (moll n t) (x - z) w : ℝ) : ℂ)) = I * (∫ z, ((fderiv ℝ (moll n t) (x - z) w : ℝ) : ℂ) * u z) - ∫ z, ((fderiv ℝ (moll n t) (x - z) (I • w) : ℝ) : ℂ) * u z`. Rewrite using `[← integral_const_mul, ← integral_sub ((hint w).const_mul I) (hint (I • w))]`. Use `congr 1`.

Use extensionality with `z`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h0` using `[hsplit]`. Take the linear combination `-h0`. Introduce `z hz`.

Establish `hxz : x - z ∉ tsupport (moll n t)` using `fun h => hz (hx (by`. Use `moll_tsupport n ht h` as an intermediate fact. Rewrite `this` using `[mem_closedBall, dist_zero_right]`. Rewrite using `[mem_closedBall, dist_eq_norm, norm_sub_rev]`. Use the proof step `linarith))`.

Establish `h0 : fderiv ℝ (moll n t) (x - z) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hxz (support_fderiv_subset ℝ (Function.mem_support.2 hne))`. Simplify using `[dbarDir, fderiv_moll_sub, h0]`.
-/
theorem mollify_differentiableAt {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} {t : ℝ} {x : V n}
    (hΩ : IsOpen Ω) (hu : Integrable u) (hw : WeakHolo Ω u) (ht : 0 < t)
    (hx : closedBall x t ⊆ Ω) :
    DifferentiableAt ℂ (mollify n t u) x := by
  have hcs := moll_hasCompactSupport n ht
  have hc1 := moll_contDiff_one n t
  have hli : LocallyIntegrable u volume := hu.locallyIntegrable
  have hD := hcs.hasFDerivAt_convolution_right (L := smulFlip) hli hc1 x
  have hcont : ∀ v, Continuous (fun a => fderiv ℝ (moll n t) a v) := fun v =>
    (hc1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint : ∀ v, Integrable (fun s => ((fderiv ℝ (moll n t) (x - s) v : ℝ) : ℂ) * u s) := by
    intro v
    have := (((hcs.fderiv_apply (𝕜 := ℝ) v).convolutionExists_right smulFlip hli (hcont v)) x)
    simpa [ConvolutionExistsAt, smulFlip_apply] using this
  rw [mollify_eq_convolution_smulFlip]
  apply differentiableAt_of_fderiv_I hD.differentiableAt
  intro w
  rw [hD.fderiv, convolution_precompR_apply smulFlip hli (hcs.fderiv (𝕜 := ℝ)) (hc1.continuous_fderiv one_ne_zero),
    convolution_precompR_apply smulFlip hli (hcs.fderiv (𝕜 := ℝ)) (hc1.continuous_fderiv one_ne_zero)]
  simp only [convolution_def, smulFlip_apply]

  have h0 := hw.2 (fun y => ((moll n t (x - y) : ℝ) : ℂ)) (isTest_moll_sub ht hx) w
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at h0
  · simp only [dbarDir, fderiv_moll_sub] at h0
    have hsplit : ∫ z, u z * (-((fderiv ℝ (moll n t) (x - z) (I • w) : ℝ) : ℂ) -
        I * -((fderiv ℝ (moll n t) (x - z) w : ℝ) : ℂ)) =
        I * (∫ z, ((fderiv ℝ (moll n t) (x - z) w : ℝ) : ℂ) * u z) -
          ∫ z, ((fderiv ℝ (moll n t) (x - z) (I • w) : ℝ) : ℂ) * u z := by
      rw [← integral_const_mul, ← integral_sub ((hint w).const_mul I) (hint (I • w))]
      congr 1
      ext z
      ring
    rw [hsplit] at h0
    linear_combination -h0
  · intro z hz
    have hxz : x - z ∉ tsupport (moll n t) := fun h => hz (hx (by
      have := moll_tsupport n ht h
      rw [mem_closedBall, dist_zero_right] at this
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
      linarith))
    have h0 : fderiv ℝ (moll n t) (x - z) = 0 := by
      by_contra hne
      exact hxz (support_fderiv_subset ℝ (Function.mem_support.2 hne))
    simp [dbarDir, fderiv_moll_sub, h0]

end ReciprocityTheory.L2DbarEstimates.C
