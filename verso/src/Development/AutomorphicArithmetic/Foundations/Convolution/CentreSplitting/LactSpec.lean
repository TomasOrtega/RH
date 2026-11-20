import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactSpec

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Introduce `K _ _ n u β hβ`. Take `⟨h, hl, -⟩` from `UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ`. Conclude with `⟨h, hl u⟩`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.lactSpec :
    UpperTheory.ConvolutionTheory.Dp.LactSpec := by
  intro K _ _ n u β hβ
  obtain ⟨h, hl, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  exact ⟨h, hl u⟩
