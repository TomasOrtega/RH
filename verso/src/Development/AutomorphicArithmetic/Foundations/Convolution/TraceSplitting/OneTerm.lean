import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.AtInj

/- English proof (translation)
Introduce `K _ _ _ n l _ μ _ θ 𝔰 V Λ t hV hθ hAt x j`. Establish `hset : {V' : Submodule ℂ (UpperTheory.ConvolutionTheory.C.LL μ) | UpperTheory.ConvolutionTheory.C.IsSummand μ V' ∧ V'.map (θ.U : UpperTheory.ConvolutionTheory.C.LL μ →ₗ[ℂ] UpperTheory.ConvolutionTheory.C.LL μ) = V' ∧ UpperTheory.ConvolutionTheory.At μ 𝔰.S V' Λ t} = {V}`. Use extensionality with `V'`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, -, h3⟩`. Conclude with `UpperTheory.ConvolutionTheory.Dp.atInj K n μ V' V h1 hV 𝔰.S 𝔰.finS t h3.2 hAt.2`. Introduce and unpack `rfl`. Conclude with `⟨hV, hθ, hAt⟩`. Unfold `UpperTheory.ConvolutionTheory.Side.tr`.

Rewrite using `[hset, finsum_mem_singleton]`.
-/
theorem UpperTheory.ConvolutionTheory.T.oneTerm :
    UpperTheory.ConvolutionTheory.T.OneTerm := by
  intro K _ _ _ n l _ μ _ θ 𝔰 V Λ t hV hθ hAt x j
  have hset : {V' : Submodule ℂ (UpperTheory.ConvolutionTheory.C.LL μ) | UpperTheory.ConvolutionTheory.C.IsSummand μ V' ∧
      V'.map (θ.U : UpperTheory.ConvolutionTheory.C.LL μ →ₗ[ℂ] UpperTheory.ConvolutionTheory.C.LL μ) = V' ∧
      UpperTheory.ConvolutionTheory.At μ 𝔰.S V' Λ t} = {V} := by
    ext V'
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact UpperTheory.ConvolutionTheory.Dp.atInj K n μ V' V h1 hV 𝔰.S 𝔰.finS t h3.2 hAt.2
    · rintro rfl
      exact ⟨hV, hθ, hAt⟩
  unfold UpperTheory.ConvolutionTheory.Side.tr
  rw [hset, finsum_mem_singleton]
