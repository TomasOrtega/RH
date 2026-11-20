import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MollifyEqConvolution

namespace ReciprocityTheory.L2DbarEstimates.C

open Metric Set Filter Topology Complex
open scoped ContDiff

/- English proof (translation)
Use `⟨{ toFun := A, map_add' := A.map_add, map_smul' := fun c w => ?_, cont := A.continuous }, ?_⟩` and prove the remaining obligations. Simplify using `only [RingHom.id_apply, smul_eq_mul] conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, A.map_add, A.map_smul, A.map_smul, hA] conv_rhs => rw [← Complex.re_add_im c]`. Simplify using `only [Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `ContinuousLinearMap.ext fun w => rfl`.
-/
theorem exists_clm_of_I {n : ℕ} (A : V n →L[ℝ] ℂ) (hA : ∀ w : V n, A (I • w) = I * A w) :
    ∃ g' : V n →L[ℂ] ℂ, g'.restrictScalars ℝ = A := by
  refine ⟨{ toFun := A, map_add' := A.map_add, map_smul' := fun c w => ?_, cont := A.continuous }, ?_⟩
  · simp only [RingHom.id_apply, smul_eq_mul]
    conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul,
      A.map_add, A.map_smul, A.map_smul, hA]
    conv_rhs => rw [← Complex.re_add_im c]
    simp only [Complex.real_smul]
    ring
  · exact ContinuousLinearMap.ext fun w => rfl

/- English proof (translation)
Introduce `n Ω f hΩ hf v x hx`. Establish `hs : ContDiffOn ℝ ∞ f Ω` using `holoSmooth n Ω f hΩ hf`. Establish `hxn : Ω ∈ 𝓝 x` using `hΩ.mem_nhds hx`. Establish `hloc : ∀ᶠ y in 𝓝 x, ∀ u : V n, fderiv ℝ f y u = fderiv ℂ f y u` using `by filter_upwards [hxn] with y hy u`. Rewrite using `[((hf y hy).differentiableAt (hΩ.mem_nhds hy)).fderiv_restrictScalars ℝ]`.

Both sides reduce to the same expression. Establish `hD2 : ContDiffAt ℝ ∞ (fderiv ℝ f) x` using `((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 hs).2.contDiffAt hxn`. Establish `hDd : DifferentiableAt ℝ (fderiv ℝ f) x` using `hD2.differentiableAt (by simp)`. Establish `hsymm : IsSymmSndFDerivAt ℝ f x` using `((contDiffOn_infty.1 hs 2).contDiffAt hxn).isSymmSndFDerivAt (by simp)`. Establish `hder : ∀ u : V n, HasFDerivAt (fun y => fderiv ℝ f y u) ((fderiv ℝ (fderiv ℝ f) x).flip u) x`.

Introduce `u`. Simplify using `using hDd.hasFDerivAt.clm_apply (hasFDerivAt_const u x)`. Establish `hI : ∀ w : V n, fderiv ℝ (fderiv ℝ f) x v (I • w) = I * fderiv ℝ (fderiv ℝ f) x v w`. Introduce `w`. Establish `hev : (fun y => fderiv ℝ f y (I • w)) =ᶠ[𝓝 x] fun y => I * fderiv ℝ f y w` using `by filter_upwards [hloc] with y hy`.

Rewrite using `[hy, hy, map_smul, smul_eq_mul]`. Establish `h2 : HasFDerivAt (fun y => I * fderiv ℝ f y w) (I • (fderiv ℝ (fderiv ℝ f) x).flip w) x` using `(hder w).const_mul I`. Establish `h3` using `((hder (I • w)).congr_of_eventuallyEq hev.symm).unique h2`. Establish `h4` using `congrArg (fun L : V n →L[ℝ] ℂ => L v) h3`. Simplify using `using h4`.

Establish `hA : ∀ w : V n, (fderiv ℝ (fderiv ℝ f) x).flip v (I • w) = I * (fderiv ℝ (fderiv ℝ f) x).flip v w`. Introduce `w`. Simplify using `only [ContinuousLinearMap.flip_apply]`. Rewrite using `[hsymm (I • w) v, hI w, hsymm w v]`. Take `⟨gC, hgC⟩` from `exists_clm_of_I _ hA`.

Establish `hev2 : (fun y => fderiv ℂ f y v) =ᶠ[𝓝 x] fun y => fderiv ℝ f y v` using `by filter_upwards [hloc] with y hy`. Conclude with `(hy v).symm`. Conclude with `((hasFDerivAt_of_restrictScalars ℝ (hder v) hgC).congr_of_eventuallyEq hev2).differentiableAt.differentiableWithinAt`.
-/
theorem holoDeriv : HoloDerivStatement := by
  intro n Ω f hΩ hf v x hx
  have hs : ContDiffOn ℝ ∞ f Ω := holoSmooth n Ω f hΩ hf
  have hxn : Ω ∈ 𝓝 x := hΩ.mem_nhds hx
  have hloc : ∀ᶠ y in 𝓝 x, ∀ u : V n, fderiv ℝ f y u = fderiv ℂ f y u := by
    filter_upwards [hxn] with y hy u
    rw [((hf y hy).differentiableAt (hΩ.mem_nhds hy)).fderiv_restrictScalars ℝ]
    rfl
  have hD2 : ContDiffAt ℝ ∞ (fderiv ℝ f) x :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 hs).2.contDiffAt hxn
  have hDd : DifferentiableAt ℝ (fderiv ℝ f) x := hD2.differentiableAt (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    ((contDiffOn_infty.1 hs 2).contDiffAt hxn).isSymmSndFDerivAt (by simp)
  have hder : ∀ u : V n, HasFDerivAt (fun y => fderiv ℝ f y u) ((fderiv ℝ (fderiv ℝ f) x).flip u) x := by
    intro u
    simpa using hDd.hasFDerivAt.clm_apply (hasFDerivAt_const u x)
  have hI : ∀ w : V n, fderiv ℝ (fderiv ℝ f) x v (I • w) = I * fderiv ℝ (fderiv ℝ f) x v w := by
    intro w
    have hev : (fun y => fderiv ℝ f y (I • w)) =ᶠ[𝓝 x] fun y => I * fderiv ℝ f y w := by
      filter_upwards [hloc] with y hy
      rw [hy, hy, map_smul, smul_eq_mul]
    have h2 : HasFDerivAt (fun y => I * fderiv ℝ f y w) (I • (fderiv ℝ (fderiv ℝ f) x).flip w) x :=
      (hder w).const_mul I
    have h3 := ((hder (I • w)).congr_of_eventuallyEq hev.symm).unique h2
    have h4 := congrArg (fun L : V n →L[ℝ] ℂ => L v) h3
    simpa using h4
  have hA : ∀ w : V n, (fderiv ℝ (fderiv ℝ f) x).flip v (I • w) =
      I * (fderiv ℝ (fderiv ℝ f) x).flip v w := by
    intro w
    simp only [ContinuousLinearMap.flip_apply]
    rw [hsymm (I • w) v, hI w, hsymm w v]
  obtain ⟨gC, hgC⟩ := exists_clm_of_I _ hA
  have hev2 : (fun y => fderiv ℂ f y v) =ᶠ[𝓝 x] fun y => fderiv ℝ f y v := by
    filter_upwards [hloc] with y hy
    exact (hy v).symm
  exact ((hasFDerivAt_of_restrictScalars ℝ (hder v) hgC).congr_of_eventuallyEq hev2).differentiableAt.differentiableWithinAt

end ReciprocityTheory.L2DbarEstimates.C
