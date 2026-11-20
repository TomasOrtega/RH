import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Introduce `K _ _ n μ _`. Establish `hr : ∀ φ : cuspForms K n, IsContRep μ (clsL μ φ) (fun y => (φ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n))` using `fun φ => isContRep_cuspToL2 μ φ`. Use `⟨fun φ hφ h => eq_zero_of_cuspVecL_eq_zero hφ (toLp_injective μ (h.trans (map_zero (toLp μ)).symm)), fun φ => (cuspToL2 μ φ).2, fun φ hφ ψ g h => ?_, fun φ _ => ?_⟩` and prove the remaining obligations. Establish `h1` using `(hr φ).translate (retractOne g)`. Establish `e : (fun y : normOneGL K n => (φ : AdelicGLn.AdelicGL K n → ℂ) ((y * retractOne g : normOneGL K n) : AdelicGLn.AdelicGL K n)) = fun y : normOneGL K n => (ψ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n)` using `funext fun y => by`.

Establish `e1 : g = (retractOne g : AdelicGLn.AdelicGL K n) * centralSection K n (detModule K n g)`. Rewrite using `[coe_retractOne, inv_mul_cancel_right]`. Rewrite using `[h]`. Use `conv_rhs => rw [e1, ← mul_assoc, apply_mul_centralSection_of_mem hφ]`. Both sides reduce to the same expression.

Establish `h2 : IsContRep μ (RG μ g (clsL μ φ)) fun y : normOneGL K n => (ψ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n)`. Rewrite using `[← e]`. Conclude with `h1`. Conclude with `Lp.ext ((hr ψ).ae_eq_quotFun.trans h2.ae_eq_quotFun.symm)`. Use `(hr φ).ae_eq_quotFun.trans (Filter.Eventually.of_forall fun y => ?_) conv_lhs => rw [← Quotient.out_eq y]` and prove the remaining obligations.

Both sides reduce to the same expression.
-/
theorem UpperTheory.ConvolutionTheory.Dp.clsBasic :
    UpperTheory.ConvolutionTheory.Dp.ClsBasic := by
  intro K _ _ n μ _
  have hr : ∀ φ : cuspForms K n, IsContRep μ (clsL μ φ)
      (fun y => (φ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n)) := fun φ => isContRep_cuspToL2 μ φ
  refine ⟨fun φ hφ h => eq_zero_of_cuspVecL_eq_zero hφ (toLp_injective μ (h.trans (map_zero (toLp μ)).symm)),
    fun φ => (cuspToL2 μ φ).2, fun φ hφ ψ g h => ?_, fun φ _ => ?_⟩
  · have h1 := (hr φ).translate (retractOne g)
    have e : (fun y : normOneGL K n => (φ : AdelicGLn.AdelicGL K n → ℂ) ((y * retractOne g : normOneGL K n) : AdelicGLn.AdelicGL K n)) =
        fun y : normOneGL K n => (ψ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n) := funext fun y => by
      have e1 : g = (retractOne g : AdelicGLn.AdelicGL K n) * centralSection K n (detModule K n g) := by
        rw [coe_retractOne, inv_mul_cancel_right]
      rw [h]
      conv_rhs => rw [e1, ← mul_assoc, apply_mul_centralSection_of_mem hφ]
      rfl
    have h2 : IsContRep μ (RG μ g (clsL μ φ)) fun y : normOneGL K n => (ψ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n) := by
      rw [← e]
      exact h1
    exact Lp.ext ((hr ψ).ae_eq_quotFun.trans h2.ae_eq_quotFun.symm)
  · refine (hr φ).ae_eq_quotFun.trans (Filter.Eventually.of_forall fun y => ?_)
    conv_lhs => rw [← Quotient.out_eq y]
    rfl
