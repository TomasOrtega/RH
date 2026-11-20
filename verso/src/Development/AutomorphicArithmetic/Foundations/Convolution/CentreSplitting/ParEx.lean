import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfEx
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatUnit
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.AutomorphicArithmetic.Foundations.Convolution.ASmooth

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Introduce `K _ _ _ n _ μ _ V hV`. Use `⟨sInfEx K n μ V hV, fun w hw => ?_, fun w B hB h0 => ?_⟩` and prove the remaining obligations. Take `⟨B, hB⟩` from `sSatEx K n μ V hV w hw`. Conclude with `⟨B, hB, (sSatUnit K n μ w V B hB).2⟩`. Take `⟨B', rfl⟩` from `(sSatUnit K n μ w V B hB).1`.

Take `⟨b, -, hb⟩` from `Multiset.mem_map.1 h0`. Conclude with `b.ne_zero hb`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.parEx :
    UpperTheory.ConvolutionTheory.ParEx := by
  intro K _ _ _ n _ μ _ V hV
  refine ⟨sInfEx K n μ V hV, fun w hw => ?_, fun w B hB h0 => ?_⟩
  · obtain ⟨B, hB⟩ := sSatEx K n μ V hV w hw
    exact ⟨B, hB, (sSatUnit K n μ w V B hB).2⟩
  · obtain ⟨B', rfl⟩ := (sSatUnit K n μ w V B hB).1
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.1 h0
    exact b.ne_zero hb
