import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Introduce `E _ _ _ n μ _ π π' V V' h h'`. Rewrite using `[isoEq E n π π']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Rewrite using `[((exSummand E n μ π V).1 h).2, ((exSummand E n μ π V').1 h').2]`.

Introduce and unpack `rfl`. Conclude with `(exCusp E n μ V h.summand).unique h h'`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.isoIff :
    UpperTheory.ConvolutionTheory.Dp.IsoIff := by
  intro E _ _ _ n μ _ π π' V V' h h'
  rw [isoEq E n π π']
  constructor
  · rintro rfl
    rw [((exSummand E n μ π V).1 h).2, ((exSummand E n μ π V').1 h').2]
  · rintro rfl
    exact (exCusp E n μ V h.summand).unique h h'
