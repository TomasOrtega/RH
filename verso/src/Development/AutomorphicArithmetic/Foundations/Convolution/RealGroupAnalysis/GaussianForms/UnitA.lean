import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

/- English proof (translation)
Introduce `F _ _ x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Establish `hinf : ∀ w, (a : A F).1 w * ((a⁻¹ : (A F)ˣ) : A F).1 w = 1` using `fun w => congrArg (fun z : A F => z.1 w) a.mul_inv`. Establish `hfin : ∀ v, (a : A F).2 v * ((a⁻¹ : (A F)ˣ) : A F).2 v = 1` using `fun v => congrArg (fun z : A F => z.2 v) a.mul_inv`.

Use `⟨fun w h => ?_, fun v h => ?_, ?_⟩` and prove the remaining obligations. Use `hinf w` as an intermediate fact. Rewrite `this` using `[h, zero_mul]`. Conclude with `zero_ne_one this`. Use `hfin v` as an intermediate fact.

Rewrite `this` using `[h, zero_mul]`. Conclude with `zero_ne_one this`. Use `filter_upwards [(a : A F).2.2, ((a⁻¹ : (A F)ˣ) : A F).2.2] with v h3 h4`. Establish `hm` using `congrArg Valued.v (hfin v)`. Rewrite `hm` using `[map_mul, map_one]`.

Use `le_antisymm h3 ?_` and prove the remaining obligations. Rewrite using `[← hm]`. Conclude with `mul_le_of_le_one_right' h4`. Introduce and unpack `⟨h1, h2, h3⟩`. Establish `hmem : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (x.2 v)⁻¹ ∈ v.adicCompletionIntegers F` using `by filter_upwards [h3] with v hv`.

Express the relevant statement in the definitionally equal form `Valued.v (x.2 v)⁻¹ ≤ 1`. Rewrite using `[map_inv₀, hv, inv_one]`. Set `y : A F` to `(fun w => (x.1 w)⁻¹, ⟨fun v => (x.2 v)⁻¹, hmem⟩)`. Use `IsUnit.of_mul_eq_one y (Prod.ext (funext fun w => ?_) ?_)` and prove the remaining obligations. Conclude with `mul_inv_cancel₀ (h1 w)`.

Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `v`. Conclude with `mul_inv_cancel₀ (h2 v)`.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.unitA :
    ∀ (F : Type) [Field F] [NumberField F] (x : A F), IsUnit x ↔ (∀ w, x.1 w ≠ 0) ∧ (∀ v, x.2 v ≠ 0) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (x.2 v) = 1 := by
  intro F _ _ x
  constructor
  · rintro ⟨a, rfl⟩
    have hinf : ∀ w, (a : A F).1 w * ((a⁻¹ : (A F)ˣ) : A F).1 w = 1 := fun w =>
      congrArg (fun z : A F => z.1 w) a.mul_inv
    have hfin : ∀ v, (a : A F).2 v * ((a⁻¹ : (A F)ˣ) : A F).2 v = 1 := fun v =>
      congrArg (fun z : A F => z.2 v) a.mul_inv
    refine ⟨fun w h => ?_, fun v h => ?_, ?_⟩
    · have := hinf w
      rw [h, zero_mul] at this
      exact zero_ne_one this
    · have := hfin v
      rw [h, zero_mul] at this
      exact zero_ne_one this
    · filter_upwards [(a : A F).2.2, ((a⁻¹ : (A F)ˣ) : A F).2.2] with v h3 h4
      have hm := congrArg Valued.v (hfin v)
      rw [map_mul, map_one] at hm
      refine le_antisymm h3 ?_
      rw [← hm]
      exact mul_le_of_le_one_right' h4
  · rintro ⟨h1, h2, h3⟩
    have hmem : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
        (x.2 v)⁻¹ ∈ v.adicCompletionIntegers F := by
      filter_upwards [h3] with v hv
      change Valued.v (x.2 v)⁻¹ ≤ 1
      rw [map_inv₀, hv, inv_one]
    let y : A F := (fun w => (x.1 w)⁻¹, ⟨fun v => (x.2 v)⁻¹, hmem⟩)
    refine IsUnit.of_mul_eq_one y (Prod.ext (funext fun w => ?_) ?_)
    · exact mul_inv_cancel₀ (h1 w)
    · apply RestrictedProduct.ext
      intro v
      exact mul_inv_cancel₀ (h2 v)
