import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.DixmierMalliavin

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

/- English proof (translation)
Introduce `K _ _ n hn U hU γ e he`. Establish `happ : ∀ x, tens γ e x = tensFun γ e x` using `(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn γ e).1`. Establish `hc : ∀ (u : U) (x : normOneGL K n), tens γ e ((finOne K n u)⁻¹ * x) = tens γ e x`. Introduce `u x`. Rewrite using `[happ, happ]`.

Unfold `tensFun`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, coe_finOne, map_mul, map_mul, map_inv, map_inv, infPart_finEmb, finPart_finEmb, inv_one, one_mul]`. Establish `h` using `he (u⁻¹ : U) (u⁻¹ : U).2 (CuspidalSpectrum.finPart K n (x : AdelicGLn.AdelicGL K n))`. Conclude with `congrArg _ h`. Use extensionality with `x`.

Rewrite using `[finAvg_apply]`. Use `haveI := compactSpace_of_isOpen U hU`. Express the relevant statement in the definitionally equal form `∫ u : U, tens γ e ((finOne K n u)⁻¹ * x) ∂haarProb U = _`. Simplify using `only [hc]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.finAvg_tens_of_leftInvariant :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
        ∀ (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
          (γ : TI K n) (e : TF K n),
          (∀ u ∈ U, ∀ h, e ((u : AdelicGLn.FiniteAdelicGL K n) * h) = e h) → finAvg U hU (tens γ e) = tens γ e := by
  intro K _ _ n hn U hU γ e he
  have happ : ∀ x, tens γ e x = tensFun γ e x := (UpperTheory.ConvolutionTheory.Tf.tensApply K n hn γ e).1
  have hc : ∀ (u : U) (x : normOneGL K n), tens γ e ((finOne K n u)⁻¹ * x) = tens γ e x := by
    intro u x
    rw [happ, happ]
    unfold tensFun
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_finOne, map_mul, map_mul, map_inv, map_inv, infPart_finEmb,
      finPart_finEmb, inv_one, one_mul]
    have h := he (u⁻¹ : U) (u⁻¹ : U).2 (CuspidalSpectrum.finPart K n (x : AdelicGLn.AdelicGL K n))
    exact congrArg _ h
  ext x
  rw [finAvg_apply]
  haveI := compactSpace_of_isOpen U hU
  change ∫ u : U, tens γ e ((finOne K n u)⁻¹ * x) ∂haarProb U = _
  simp only [hc]
  simp
