import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SatIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TsphVec
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatUnit
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Introduce `E _ _ _ n μ _ π V h w B`. Prove the components needed by the constructor for the conclusion. Introduce `hB`. Take `⟨B', rfl⟩` from `(sSatUnit E n μ w V B hB).1`. Conclude with `⟨B', rfl, (satIff E n μ π V h w B').2 ((tsphVec E n μ w V h.summand B').2 hB)⟩`.

Introduce and unpack `⟨B', rfl, hB⟩`. Conclude with `(tsphVec E n μ w V h.summand B').1 ((satIff E n μ π V h w B').1 hB)`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.sSatIff :
    UpperTheory.ConvolutionTheory.Dp.SSatIff := by
  intro E _ _ _ n μ _ π V h w B
  constructor
  · intro hB
    obtain ⟨B', rfl⟩ := (sSatUnit E n μ w V B hB).1
    exact ⟨B', rfl, (satIff E n μ π V h w B').2 ((tsphVec E n μ w V h.summand B').2 hB)⟩
  · rintro ⟨B', rfl, hB⟩
    exact (tsphVec E n μ w V h.summand B').1 ((satIff E n μ π V h w B').1 hB)
