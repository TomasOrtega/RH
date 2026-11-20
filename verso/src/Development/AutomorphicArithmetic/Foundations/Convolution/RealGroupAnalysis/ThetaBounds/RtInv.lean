import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

/- English proof (translation)
Introduce `F _ _ _ M u hu k`. Use `haveI := M.haar`. Use `haveI := M.right`. Establish `hmp : MeasurePreserving (· * k) M.μ M.μ` using `measurePreserving_mul_right M.μ k`. Establish `hemb : MeasurableEmbedding (· * k : G1 F → G1 F)` using `(MeasurableEquiv.mulRight k).measurableEmbedding`.

Establish `hfd : IsFundamentalDomain (Gam F) ((Equiv.mulRight k) '' M.D) M.μ`. Use `M.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_` and prove the remaining obligations. Conclude with `(measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving`. Introduce `g x`. Simplify using `[Subgroup.smul_def, mul_assoc]`.

Establish `hinv : ∀ (g : Gam F) x, u (g • x) = u x`. Introduce and unpack `⟨_, γ, rfl⟩ x`. Simplify `hu γ x` using `[Subgroup.smul_def]`. Establish `hpre : (· * k : G1 F → G1 F) ⁻¹' ((Equiv.mulRight k) '' M.D) = M.D`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Establish `h3` using `hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)`. Rewrite `h3` using `[hpre]`. Rewrite using `[h3]`. Conclude with `hfd.setIntegral_eq M.fund hinv`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.rtInv :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], RtInv F := by
  intro F _ _ _ M u hu k
  haveI := M.haar
  haveI := M.right
  have hmp : MeasurePreserving (· * k) M.μ M.μ := measurePreserving_mul_right M.μ k
  have hemb : MeasurableEmbedding (· * k : G1 F → G1 F) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd : IsFundamentalDomain (Gam F) ((Equiv.mulRight k) '' M.D) M.μ := by
    refine M.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_
    · exact (measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving
    · intro g x
      simp [Subgroup.smul_def, mul_assoc]
  have hinv : ∀ (g : Gam F) x, u (g • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    simpa [Subgroup.smul_def] using hu γ x
  have hpre : (· * k : G1 F → G1 F) ⁻¹' ((Equiv.mulRight k) '' M.D) = M.D := by
    ext x; simp
  have h3 := hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)
  rw [hpre] at h3
  rw [h3]
  exact hfd.setIntegral_eq M.fund hinv
