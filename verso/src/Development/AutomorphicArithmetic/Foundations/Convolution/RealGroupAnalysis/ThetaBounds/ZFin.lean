import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Cap

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W M π hreg Φ hΦ`. Establish `hcap` using `UpperTheory.ConvolutionTheory.R2.cap F E D W M π`. Establish `key : ∀ z ∈ GlobalTheory.CuspRep.Zalg E 2, ∃ c : ℂ, z Φ = c • Φ`. Introduce `z hz`. Proceed by induction on `hz using Algebra.adjoin_induction with`.

Consider the case `mem x hx`. Take `⟨τ, u, rfl⟩` from `hx`. Take `⟨m, hm, -⟩` from `hreg (InfinitePlace.mk (τ.comp (algebraMap F E)))`. Conclude with `⟨_, hcap τ m hm u Φ hΦ⟩`. Consider the case `algebraMap r => exact ⟨r, by simp [Module.algebraMap_end_apply]⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by rw [LinearMap.add_apply, ha, hb, add_smul]⟩`. Consider the case `mul x y _ _ hx hy`.

Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨b * a, by rw [Module.End.mul_apply, hb, map_smul, ha, mul_smul]⟩`. Establish `hle : Submodule.span ℂ ((fun z : Module.End ℂ (Sm E 2) => z Φ) '' GlobalTheory.CuspRep.Zalg E 2) ≤ Submodule.span ℂ {Φ}` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨z, hz, rfl⟩`.

Take `⟨c, hc⟩` from `key z hz`. Express the relevant statement in the definitionally equal form `z Φ ∈ Submodule.span ℂ {Φ}`. Rewrite using `[hc]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self Φ))`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.zFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ZFin W M π := by
  intro F E _ _ _ _ _ _ _ D W M π hreg Φ hΦ
  have hcap := UpperTheory.ConvolutionTheory.R2.cap F E D W M π
  have key : ∀ z ∈ GlobalTheory.CuspRep.Zalg E 2, ∃ c : ℂ, z Φ = c • Φ := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨τ, u, rfl⟩ := hx
      obtain ⟨m, hm, -⟩ := hreg (InfinitePlace.mk (τ.comp (algebraMap F E)))
      exact ⟨_, hcap τ m hm u Φ hΦ⟩
    | algebraMap r => exact ⟨r, by simp [Module.algebraMap_end_apply]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [LinearMap.add_apply, ha, hb, add_smul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨b * a, by rw [Module.End.mul_apply, hb, map_smul, ha, mul_smul]⟩
  have hle : Submodule.span ℂ ((fun z : Module.End ℂ (Sm E 2) => z Φ) '' GlobalTheory.CuspRep.Zalg E 2) ≤
      Submodule.span ℂ {Φ} := Submodule.span_le.2 (by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, hc⟩ := key z hz
    change z Φ ∈ Submodule.span ℂ {Φ}
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self Φ))
  exact Submodule.finiteDimensional_of_le hle
