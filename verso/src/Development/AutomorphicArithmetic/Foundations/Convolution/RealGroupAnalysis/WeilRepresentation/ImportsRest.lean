import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RedDet
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.FromGL

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `F _ _ _`. Take `⟨t₀, ht₀, h⟩` from `Reduction.exists_reduced (K := F)`. Use `⟨Real.sqrt t₀, Real.sqrt_pos.2 ht₀, fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, b, hb, k, hk, he, hr⟩` from `h 2 (gl g)`. Take `⟨γ', b', hb', he', h0, h1⟩` from `M.redDet F g γ b hb k he`.

Take `⟨x, a, k', hk', hg, ha, ha'⟩` from `M.fromGL F (ratS F γ' * g) b' hb' k hk he'`. Use `⟨γ', x, a, k', hk', hg, ?_⟩` and prove the remaining obligations. Use `hr 0 1 rfl` as an intermediate fact. Rewrite `this` using `[← h1, ← h0, ha', ← ha, Reduction.adeleAbs_units]`. Express the relevant statement in the definitionally equal form `t₀ * (ab a)⁻¹ ≤ ab a at this`.

Establish `hp` using `M.ab_pos a`. Rewrite `this` using `[mul_inv_le_iff₀ hp]`. Conclude with `Real.sqrt_le_iff.2 ⟨hp.le, by rwa [pow_two]⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.red :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], St.Red F := by
  intro F _ _ _
  obtain ⟨t₀, ht₀, h⟩ := Reduction.exists_reduced (K := F)
  refine ⟨Real.sqrt t₀, Real.sqrt_pos.2 ht₀, fun g => ?_⟩
  obtain ⟨γ, b, hb, k, hk, he, hr⟩ := h 2 (gl g)
  obtain ⟨γ', b', hb', he', h0, h1⟩ := M.redDet F g γ b hb k he
  obtain ⟨x, a, k', hk', hg, ha, ha'⟩ := M.fromGL F (ratS F γ' * g) b' hb' k hk he'
  refine ⟨γ', x, a, k', hk', hg, ?_⟩
  have := hr 0 1 rfl
  rw [← h1, ← h0, ha', ← ha, Reduction.adeleAbs_units] at this
  change t₀ * (ab a)⁻¹ ≤ ab a at this
  have hp := M.ab_pos a
  rw [mul_inv_le_iff₀ hp] at this
  exact Real.sqrt_le_iff.2 ⟨hp.le, by rwa [pow_two]⟩
