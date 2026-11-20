import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

section Kernel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

/- English proof (translation)
Establish `hT : T2Space (RightCosetSpace Γ)` using `RightCosetSpace.t2Space Γ`. Establish `hC : IsCompact (mk Γ '' ((a * ·) '' tsupport (f : G → ℂ)))` using `(f.hasCompactSupport.isCompact.image (continuous_const_mul a)).image (continuous_mk Γ)`. Use `HasCompactSupport.intro hC fun q hq => ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `mk_surjective Γ q`. Rewrite using `[quotientKernel_mk]`.

Use `finsum_eq_zero_of_forall_eq_zero fun γ => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `hq ⟨(γ : G) * b, ⟨a⁻¹ * γ * b, subset_tsupport _ h, ?_⟩, mk_mul_of_mem γ.2 b⟩` and prove the remaining obligations. Simplify using `[mul_assoc]`.
-/
private theorem hasCompactSupport_kernel (f : CompactlySupportedContinuousMap G ℂ) (a : G) :
    HasCompactSupport fun q => quotientKernel Γ f (mk Γ a, q) := by
  have hT : T2Space (RightCosetSpace Γ) := RightCosetSpace.t2Space Γ
  have hC : IsCompact (mk Γ '' ((a * ·) '' tsupport (f : G → ℂ))) :=
    (f.hasCompactSupport.isCompact.image (continuous_const_mul a)).image (continuous_mk Γ)
  refine HasCompactSupport.intro hC fun q hq => ?_
  obtain ⟨b, rfl⟩ := mk_surjective Γ q
  rw [quotientKernel_mk]
  refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
  by_contra h
  refine hq ⟨(γ : G) * b, ⟨a⁻¹ * γ * b, subset_tsupport _ h, ?_⟩, mk_mul_of_mem γ.2 b⟩
  simp [mul_assoc]

/- English proof (translation)
Establish `hint : Integrable (fun y => φ (mk Γ y) * f (a⁻¹ * y)) μ`. Simplify `integrable_rconv Γ μ f φ a` using `only [mul_comm]`. Establish `h1 : rconv Γ μ f φ a = ∫ y, φ (mk Γ y) * f (a⁻¹ * y) ∂μ`. Unfold `rconv`. Simplify using `only [mul_comm]`.

Rewrite using `[h1, integral_mul_eq_integral_mul_automorphize μ hint]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Take `⟨b, rfl⟩` from `mk_surjective Γ y`. Simplify using `only`. Rewrite using `[quotientKernel_mk]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `∑' γ : Γ, f (a⁻¹ * (γ • b)) = _`. Repeatedly rewrite using `[Subgroup.smul_def, smul_eq_mul, ← mul_assoc]`. Conclude with `tsum_eq_finsum (finite_support_automorphicKernel Γ f (a, b))`.
-/
private theorem rconv_eq_integral_kernel (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (a : G) :
    rconv Γ μ f φ a = ∫ q, φ q * quotientKernel Γ f (mk Γ a, q) ∂quotientMeasure Γ μ := by
  have hint : Integrable (fun y => φ (mk Γ y) * f (a⁻¹ * y)) μ := by
    simpa only [mul_comm] using integrable_rconv Γ μ f φ a
  have h1 : rconv Γ μ f φ a = ∫ y, φ (mk Γ y) * f (a⁻¹ * y) ∂μ := by
    unfold rconv
    simp only [mul_comm]
  rw [h1, integral_mul_eq_integral_mul_automorphize μ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  obtain ⟨b, rfl⟩ := mk_surjective Γ y
  dsimp only
  rw [quotientKernel_mk]
  congr 1
  change ∑' γ : Γ, f (a⁻¹ * (γ • b)) = _
  simp_rw [Subgroup.smul_def, smul_eq_mul, ← mul_assoc]
  exact tsum_eq_finsum (finite_support_automorphicKernel Γ f (a, b))

end Kernel

/- English proof (translation)
Introduce `K _ _ n μ _ f x`. Establish `hc : Continuous fun q => quotientKernel (Gam K n) f (mk (Gam K n) x, q)` using `(continuous_quotientKernel (Gam K n) f).comp (continuous_const.prodMk continuous_id)`. Establish `hcs` using `hasCompactSupport_kernel (Gam K n) f x`. Establish `hm : MemLp (fun q => (starRingEnd ℂ) (quotientKernel (Gam K n) f (mk (Gam K n) x, q))) 2 (quotientMeasure (Gam K n) μ)` using `(Complex.continuous_conj.comp hc).memLp_of_hasCompactSupport (hcs.comp_left (g := starRingEnd ℂ) (map_zero _))`. Establish `hkw : kv μ f x = hm.toLp _`.

Use `ext_inner_right ℂ fun φ => ?_` and prove the remaining obligations. Rewrite using `[inner_kv, rconv_eq_integral_kernel, L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hm.coeFn_toLp] with q hq`. Rewrite using `[hq, RCLike.inner_apply', Complex.conj_conj, mul_comm]`.

Rewrite using `[hkw]`. Conclude with `hm.coeFn_toLp`.
-/
theorem UpperTheory.ConvolutionTheory.K.kvAe :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f : CC K n) (x : G1 K n),
      (kv μ f x : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
        fun y => (starRingEnd ℂ) (quotientKernel (Gam K n) f (mk (Gam K n) x, y)) := by
  intro K _ _ n μ _ f x
  have hc : Continuous fun q => quotientKernel (Gam K n) f (mk (Gam K n) x, q) :=
    (continuous_quotientKernel (Gam K n) f).comp (continuous_const.prodMk continuous_id)
  have hcs := hasCompactSupport_kernel (Gam K n) f x
  have hm : MemLp (fun q => (starRingEnd ℂ) (quotientKernel (Gam K n) f (mk (Gam K n) x, q))) 2
      (quotientMeasure (Gam K n) μ) :=
    (Complex.continuous_conj.comp hc).memLp_of_hasCompactSupport
      (hcs.comp_left (g := starRingEnd ℂ) (map_zero _))
  have hkw : kv μ f x = hm.toLp _ := by
    refine ext_inner_right ℂ fun φ => ?_
    rw [inner_kv, rconv_eq_integral_kernel, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with q hq
    rw [hq, RCLike.inner_apply', Complex.conj_conj, mul_comm]
  rw [hkw]
  exact hm.coeFn_toLp
