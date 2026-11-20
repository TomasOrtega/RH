import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsTw
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ConjCarries
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.GalCentral
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceC

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Introduce `E _ _ _ n μ _ θ σ s hs he π V hV`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨P', hsp, hiso⟩` from `h s hs`. Consider the cases of `P' with`.

Consider the case `cx π'`. Establish `e : π' = π` using `(UpperTheory.ConvolutionTheory.Dp.isoEq E n π' π).1 hiso`. Substitute `e` using the available equality. Establish `h1` using `(UpperTheory.ConvolutionTheory.Dp.conjCarries E n μ θ σ s hs he π' π' V hsp).1 hV`. Conclude with `((UpperTheory.ConvolutionTheory.Dp.exSummand E n μ π' _).1 h1).2.trans ((UpperTheory.ConvolutionTheory.Dp.exSummand E n μ π' _).1 hV).2.symm`.

Consider the case `re π' => exact hiso.elim`. Introduce `h s' hs'`. Take `rfl : s' = s` from `(UpperTheory.ConvolutionTheory.Dp.galCentral E n σ s hs).1 s' hs'`. Take `⟨π', hsp⟩` from `UpperTheory.CBC.SConjSpaceC_holds E σ s' hs n π`. Establish `h1 : Carries μ π' V` using `(UpperTheory.ConvolutionTheory.Dp.conjCarries E n μ θ σ s' hs he π π' V hsp).2 (by rw [h]; exact hV)`.

Establish `e : π' = π` using `(UpperTheory.ConvolutionTheory.Dp.exCusp E n μ V hV.summand).unique h1 hV`. Conclude with `⟨.cx π', hsp, (UpperTheory.ConvolutionTheory.Dp.isoEq E n π' π).2 e⟩`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.conjIff :
    UpperTheory.ConvolutionTheory.Dp.ConjIff := by
  intro E _ _ _ n μ _ θ σ s hs he π V hV
  constructor
  · intro h
    obtain ⟨P', hsp, hiso⟩ := h s hs
    cases P' with
    | cx π' =>
      have e : π' = π := (UpperTheory.ConvolutionTheory.Dp.isoEq E n π' π).1 hiso
      subst e
      have h1 := (UpperTheory.ConvolutionTheory.Dp.conjCarries E n μ θ σ s hs he π' π' V hsp).1 hV
      exact ((UpperTheory.ConvolutionTheory.Dp.exSummand E n μ π' _).1 h1).2.trans ((UpperTheory.ConvolutionTheory.Dp.exSummand E n μ π' _).1 hV).2.symm
    | re π' => exact hiso.elim
  · intro h s' hs'
    obtain rfl : s' = s := (UpperTheory.ConvolutionTheory.Dp.galCentral E n σ s hs).1 s' hs'
    obtain ⟨π', hsp⟩ := UpperTheory.CBC.SConjSpaceC_holds E σ s' hs n π
    have h1 : Carries μ π' V :=
      (UpperTheory.ConvolutionTheory.Dp.conjCarries E n μ θ σ s' hs he π π' V hsp).2 (by rw [h]; exact hV)
    have e : π' = π := (UpperTheory.ConvolutionTheory.Dp.exCusp E n μ V hV.summand).unique h1 hV
    exact ⟨.cx π', hsp, (UpperTheory.ConvolutionTheory.Dp.isoEq E n π' π).2 e⟩
