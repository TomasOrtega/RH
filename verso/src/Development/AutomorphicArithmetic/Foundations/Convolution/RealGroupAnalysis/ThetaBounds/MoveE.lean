import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CurveE
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OpsFock
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Mov

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D O W M π f hf φ hφ w h`. Take `⟨G, c, hc, hG, hd⟩` from `curveE F E D O W w`. Establish `hx` using `fun i ψ hψ => (opsFock F E D O w i ψ hψ).1`. Establish `he : O.e D.δ w φ ∈ Fock D.δ` using `Submodule.smul_mem _ _ (sub_mem (sub_mem (hx _ _ (hx _ _ hφ)) (Submodule.smul_mem _ _ (hx _ _ (hx _ _ hφ)))) (hx _ _ (hx _ _ hφ)))`. Conclude with `congrFun (mov F E D W M π f hf φ hφ _ he G c _ hc hG (hd φ)) h`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.moveE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Fo.MoveE O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ w h
  obtain ⟨G, c, hc, hG, hd⟩ := curveE F E D O W w
  have hx := fun i ψ hψ => (opsFock F E D O w i ψ hψ).1
  have he : O.e D.δ w φ ∈ Fock D.δ :=
    Submodule.smul_mem _ _ (sub_mem (sub_mem (hx _ _ (hx _ _ hφ)) (Submodule.smul_mem _ _ (hx _ _ (hx _ _ hφ)))) (hx _ _ (hx _ _ hφ)))
  exact congrFun (mov F E D W M π f hf φ hφ _ he G c _ hc hG (hd φ)) h
