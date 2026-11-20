import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

open GlobalTheory.CuspRep in
/- English proof (translation)
Introduce `E _ _ _ n μ _ V hV τ`. Take `⟨π, hπ, -⟩` from `exCusp E n μ V hV`. Use `⟨(CG.mk π).infChar τ, (sInfIff E n μ π V hπ τ _).2 (ParLaws.hasInfChar_infChar (CG.mk π) τ), fun m hm => ?_⟩` and prove the remaining obligations. Conclude with `(CG.HasInfChar.infChar_eq (π := CG.mk π) ((sInfIff E n μ π V hπ τ m).1 hm)).symm`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.sInfEx :
    UpperTheory.ConvolutionTheory.Dp.SInfEx := by
  intro E _ _ _ n μ _ V hV τ
  obtain ⟨π, hπ, -⟩ := exCusp E n μ V hV
  refine ⟨(CG.mk π).infChar τ, (sInfIff E n μ π V hπ τ _).2 (ParLaws.hasInfChar_infChar (CG.mk π) τ), fun m hm => ?_⟩
  exact (CG.HasInfChar.infChar_eq (π := CG.mk π) ((sInfIff E n μ π V hπ τ m).1 hm)).symm
