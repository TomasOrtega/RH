import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.SummableRationalSchwartz
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W M π`. Establish `hc` using `UpperTheory.ConvolutionTheory.R2.conv F E D W M π`. Take `⟨hadd, hsmul⟩` from `UpperTheory.ConvolutionTheory.R2.Ff.thLin F`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f hf φ hφ φ' hφ'`.

Use function extensionality and compare the values at `h`. Establish `e : ∀ g, f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (φ + φ'))).1 = f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1 + f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ')).1`. Introduce `g`. Rewrite using `[map_add, map_add, hadd, mul_add]`. Simplify using `only [lift, e, Pi.add_apply]`.

Conclude with `integral_add (hc f hf φ hφ h).1 (hc f hf φ' hφ' h).1`. Introduce `f c φ`. Use function extensionality and compare the values at `h`. Establish `e : ∀ g, f (gl g * dM (nu F h)) * Th (W.Om g (W.L h (c • φ))).1 = c * (f (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1)`. Introduce `g`.

Rewrite using `[map_smul, map_smul, hsmul, mul_left_comm]`. Simplify using `only [lift, e, Pi.smul_apply, smul_eq_mul]`. Conclude with `integral_const_mul c _`. Introduce `f hf f' hf' φ hφ`. Use function extensionality and compare the values at `h`.

Establish `e : ∀ g, (f + f').1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1 = f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1 + f'.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1`. Introduce `g`. Conclude with `add_mul _ _ _`. Simplify using `only [lift, e, Pi.add_apply]`. Conclude with `integral_add (hc f hf φ hφ h).1 (hc f' hf' φ hφ h).1`.

Introduce `f c φ`. Use function extensionality and compare the values at `h`. Simplify using `only [lift, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Conclude with `integral_const_mul c _`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.lin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Lin W M π := by
  intro F E _ _ _ _ _ _ _ D W M π
  have hc := UpperTheory.ConvolutionTheory.R2.conv F E D W M π
  obtain ⟨hadd, hsmul⟩ := UpperTheory.ConvolutionTheory.R2.Ff.thLin F
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf φ hφ φ' hφ'
    funext h
    have e : ∀ g, f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (φ + φ'))).1 =
        f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1 +
          f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ')).1 := by
      intro g
      rw [map_add, map_add, hadd, mul_add]
    simp only [lift, e, Pi.add_apply]
    exact integral_add (hc f hf φ hφ h).1 (hc f hf φ' hφ' h).1
  · intro f c φ
    funext h
    have e : ∀ g, f (gl g * dM (nu F h)) * Th (W.Om g (W.L h (c • φ))).1 =
        c * (f (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1) := by
      intro g
      rw [map_smul, map_smul, hsmul, mul_left_comm]
    simp only [lift, e, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  · intro f hf f' hf' φ hφ
    funext h
    have e : ∀ g, (f + f').1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1 =
        f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1 +
          f'.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1 := by
      intro g
      exact add_mul _ _ _
    simp only [lift, e, Pi.add_apply]
    exact integral_add (hc f hf φ hφ h).1 (hc f' hf' φ hφ h).1
  · intro f c φ
    funext h
    simp only [lift, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
