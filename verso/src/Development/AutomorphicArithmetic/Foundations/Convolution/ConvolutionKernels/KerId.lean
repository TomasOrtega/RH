import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAdj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RconvEqIntegralKernel
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

/- English proof (translation)
Introduce `K _ _ n μ _ f a g M hf x y`. Use `haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ`. Establish `ext : ∀ u w : RightCosetSpace (Gam K n) → ℂ, Continuous u → Continuous w → u =ᵐ[quotientMeasure (Gam K n) μ] w → ∀ z : G1 K n, u (mk _ z) = w (mk _ z)`. Introduce `u w hu hw h z`. Establish `h1` using `(quasiMeasurePreserving_mk (Gam K n) μ).ae_eq_comp h`.

Conclude with `congrFun ((hu.comp (continuous_mk _)).ae_eq_iff_eq μ (hw.comp (continuous_mk _)) |>.1 h1) z`. Establish `s1 : ∀ φ : L2 μ, rconv (Gam K n) μ f φ x = rconv (Gam K n) μ a (M (Rop μ g φ)) x`. Introduce `φ`. Establish `e : Rop μ f φ = Rop μ a (M (Rop μ g φ))` using `by rw [hf]; rfl`. Use `ext _ _ (continuous_rconvQ _ μ f φ) (continuous_rconvQ _ μ a _) ?_ x` and prove the remaining obligations.

Establish `a1` using `integrated_ae_eq_rconvQ (Gam K n) μ f φ`. Establish `a2` using `integrated_ae_eq_rconvQ (Gam K n) μ a (M (Rop μ g φ))`. Express the relevant statement in the definitionally equal form `(Rop μ f φ : _ → ℂ) =ᵐ[_] _ at a1`. Express the relevant statement in the definitionally equal form `(Rop μ a (M (Rop μ g φ)) : _ → ℂ) =ᵐ[_] _ at a2`. Rewrite `a1` using `[e]`.

Conclude with `a1.symm.trans a2`. Establish `s2 : kv μ f x = Rop μ (ccStar g) (ContinuousLinearMap.adjoint M (kv μ a x))`. Use `ext_inner_right ℂ fun φ => ?_` and prove the remaining obligations. Rewrite using `[inner_kv, s1, ← ropAdj, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, inner_kv]`. Establish `a3` using `integrated_ae_eq_rconvQ (Gam K n) μ (ccStar g) (ContinuousLinearMap.adjoint M (kv μ a x))`.

Express the relevant statement in the definitionally equal form `(Rop μ (ccStar g) _ : _ → ℂ) =ᵐ[_] _ at a3`. Rewrite `a3` using `[← s2]`. Establish `s3` using `ext _ _ (Complex.continuous_conj.comp ((continuous_quotientKernel (Gam K n) f).comp (Continuous.prodMk_right (mk _ x)))) (continuous_rconvQ _ μ (ccStar g) _) ((kvAe K n μ f x).symm.trans a3) y`. Simplify using `only [Function.comp_apply, quotientKernel_mk, rconvQ_mk] at s3`. Rewrite `s3` using `[← inner_kv, ContinuousLinearMap.adjoint_inner_right]`.

Rewrite using `[← inner_conj_symm, ← s3, starRingEnd_self_apply]`.
-/
theorem UpperTheory.ConvolutionTheory.K.kerId :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f a g : CC K n) (M : L2 μ →L[ℂ] L2 μ),
      Rop μ f = Rop μ a ∘L M ∘L Rop μ g → ∀ x y : G1 K n,
        ∑ᶠ γ : Gam K n, f (x⁻¹ * (γ : G1 K n) * y) = ⟪kv μ a x, M (kv μ (ccStar g) y)⟫_ℂ := by
  intro K _ _ n μ _ f a g M hf x y
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have ext : ∀ u w : RightCosetSpace (Gam K n) → ℂ, Continuous u → Continuous w →
      u =ᵐ[quotientMeasure (Gam K n) μ] w → ∀ z : G1 K n, u (mk _ z) = w (mk _ z) := by
    intro u w hu hw h z
    have h1 := (quasiMeasurePreserving_mk (Gam K n) μ).ae_eq_comp h
    exact congrFun ((hu.comp (continuous_mk _)).ae_eq_iff_eq μ (hw.comp (continuous_mk _)) |>.1 h1) z
  have s1 : ∀ φ : L2 μ, rconv (Gam K n) μ f φ x = rconv (Gam K n) μ a (M (Rop μ g φ)) x := by
    intro φ
    have e : Rop μ f φ = Rop μ a (M (Rop μ g φ)) := by rw [hf]; rfl
    refine ext _ _ (continuous_rconvQ _ μ f φ) (continuous_rconvQ _ μ a _) ?_ x
    have a1 := integrated_ae_eq_rconvQ (Gam K n) μ f φ
    have a2 := integrated_ae_eq_rconvQ (Gam K n) μ a (M (Rop μ g φ))
    change (Rop μ f φ : _ → ℂ) =ᵐ[_] _ at a1
    change (Rop μ a (M (Rop μ g φ)) : _ → ℂ) =ᵐ[_] _ at a2
    rw [e] at a1
    exact a1.symm.trans a2
  have s2 : kv μ f x = Rop μ (ccStar g) (ContinuousLinearMap.adjoint M (kv μ a x)) := by
    refine ext_inner_right ℂ fun φ => ?_
    rw [inner_kv, s1, ← ropAdj, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, inner_kv]
  have a3 := integrated_ae_eq_rconvQ (Gam K n) μ (ccStar g) (ContinuousLinearMap.adjoint M (kv μ a x))
  change (Rop μ (ccStar g) _ : _ → ℂ) =ᵐ[_] _ at a3
  rw [← s2] at a3
  have s3 := ext _ _ (Complex.continuous_conj.comp ((continuous_quotientKernel (Gam K n) f).comp (Continuous.prodMk_right (mk _ x))))
    (continuous_rconvQ _ μ (ccStar g) _) ((kvAe K n μ f x).symm.trans a3) y
  simp only [Function.comp_apply, quotientKernel_mk, rconvQ_mk] at s3
  rw [← inner_kv, ContinuousLinearMap.adjoint_inner_right] at s3
  rw [← inner_conj_symm, ← s3, starRingEnd_self_apply]
