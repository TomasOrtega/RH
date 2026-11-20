import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsTw
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistUnitary

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.Dp.twUnitary :
    UpperTheory.ConvolutionTheory.Dp.TwUnitary := by
  intro K _ _ n μ _ θ
  obtain ⟨U, hU, hint, -⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary K n μ θ
  have h : ∀ v, θ.U v = U v := fun v => by rw [← hU]; rfl
  refine ⟨fun v => ?_, fun w => ?_, fun g v => ?_⟩
  · rw [h]; exact U.norm_map v
  · obtain ⟨v, hv⟩ := U.surjective w
    exact ⟨v, (h v).trans hv⟩
  · rw [h, h]; exact hint g v
