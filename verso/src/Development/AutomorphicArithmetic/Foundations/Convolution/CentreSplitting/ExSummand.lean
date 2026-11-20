import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsClosure
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ClosureSummand
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Introduce `E _ _ _ n μ _ π V`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨h.carrier_eq ▸ inf_le_left, ?_⟩` and prove the remaining obligations. Rewrite using `[h.carrier_eq, (formsIrr E n μ V h.summand).2.2.2]`.

Introduce and unpack `⟨hc, rfl⟩`. Take `⟨hne, hirr⟩` from `(Cm.stab_carrier π).isIrreducible_iff.1 (Cm.isIrreducible_toModule π)`. Conclude with `⟨closureSummand E n μ _ hc (Cm.stab_carrier π) hne hirr, (formsClosure E n μ _ hc (Cm.stab_carrier π)).symm⟩`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.exSummand :
    UpperTheory.ConvolutionTheory.Dp.ExSummand := by
  intro E _ _ _ n μ _ π V
  constructor
  · intro h
    refine ⟨h.carrier_eq ▸ inf_le_left, ?_⟩
    rw [h.carrier_eq, (formsIrr E n μ V h.summand).2.2.2]
  · rintro ⟨hc, rfl⟩
    obtain ⟨hne, hirr⟩ := (Cm.stab_carrier π).isIrreducible_iff.1 (Cm.isIrreducible_toModule π)
    exact ⟨closureSummand E n μ _ hc (Cm.stab_carrier π) hne hirr, (formsClosure E n μ _ hc (Cm.stab_carrier π)).symm⟩
