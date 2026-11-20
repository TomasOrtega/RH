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
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
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
