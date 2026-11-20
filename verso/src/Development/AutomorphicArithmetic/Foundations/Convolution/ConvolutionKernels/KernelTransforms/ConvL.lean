import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.TraceFormulaConvolution
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.DerivInt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InvSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Unimod
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CenterTr
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.ExpGen

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

/- English proof (translation)
Introduce `K _ _ n ν _ β₁ β₂ h₁`. Establish `hc : HasCompactSupport (fun g : archGroup K n => β₁ g⁻¹)` using `β₁.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)`. Establish `hΘ : Continuous (fun c : archGroup K n => β₂ c⁻¹)` using `(map_continuous β₂).comp continuous_inv`. Take `⟨hF, hD⟩` from `UpperTheory.ConvolutionTheory.Tf.derivInt K n ν (fun g => β₁ g⁻¹) h₁ hc (fun c => β₂ c⁻¹) hΘ`. Establish `e : (fun x : archGroup K n => ∫ a, (fun g : archGroup K n => β₁ g⁻¹) (a⁻¹ * x) * (fun c : archGroup K n => β₂ c⁻¹) a ∂ν) = fun g => conv ν β₁ β₂ g⁻¹`.

Use function extensionality and compare the values at `g`. Rewrite using `[GroundTheory.Automorphic.conv_apply, ← integral_mul_left_eq_self (μ := ν) (fun a => β₁ a * β₂ (a⁻¹ * g⁻¹)) g⁻¹]`. Use `congr 1`. Use function extensionality and compare the values at `c`. Simplify using `[mul_assoc]`.

Use `⟨e ▸ hF, fun u x => ?_⟩` and prove the remaining obligations. Use `Eq.trans (congrArg (fun f => (((isExpLieAlgebra K n).rightUAction u f : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) : archGroup K n → ℂ) x⁻¹) (Subtype.ext e.symm : _ = (⟨_, hF⟩ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)))) ?_` and prove the remaining obligations. Rewrite using `[hD u x⁻¹, ← integral_mul_left_eq_self (μ := ν) (fun a => ((isExpLieAlgebra K n).rightUAction u ⟨fun g => β₁ g⁻¹, h₁⟩ : archGroup K n → ℂ) a⁻¹ * β₂ (a⁻¹ * x)) x]`. Use `congr 1`. Use function extensionality and compare the values at `c`.

Simplify using `[mul_assoc]`.
-/
theorem UpperTheory.ConvolutionTheory.Tf.convL :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β₁ β₂ : CompactlySupportedContinuousMap (archGroup K n) ℂ)
      (h₁ : (fun g => β₁ g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)), ∃ h₁₂ : (fun g => conv ν β₁ β₂ g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ), ∀ (u : UEnv K n) (x : archGroup K n),
        ((isExpLieAlgebra K n).rightUAction u ⟨fun g => conv ν β₁ β₂ g⁻¹, h₁₂⟩ : archGroup K n → ℂ) x⁻¹ =
          ∫ a, ((isExpLieAlgebra K n).rightUAction u ⟨fun g => β₁ g⁻¹, h₁⟩ : archGroup K n → ℂ) a⁻¹ * β₂ (a⁻¹ * x) ∂ν := by
  intro K _ _ n ν _ β₁ β₂ h₁
  have hc : HasCompactSupport (fun g : archGroup K n => β₁ g⁻¹) :=
    β₁.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)
  have hΘ : Continuous (fun c : archGroup K n => β₂ c⁻¹) := (map_continuous β₂).comp continuous_inv
  obtain ⟨hF, hD⟩ := UpperTheory.ConvolutionTheory.Tf.derivInt K n ν (fun g => β₁ g⁻¹) h₁ hc (fun c => β₂ c⁻¹) hΘ
  have e : (fun x : archGroup K n => ∫ a, (fun g : archGroup K n => β₁ g⁻¹) (a⁻¹ * x) * (fun c : archGroup K n => β₂ c⁻¹) a ∂ν) =
      fun g => conv ν β₁ β₂ g⁻¹ := by
    funext g
    rw [GroundTheory.Automorphic.conv_apply,
      ← integral_mul_left_eq_self (μ := ν) (fun a => β₁ a * β₂ (a⁻¹ * g⁻¹)) g⁻¹]
    congr 1
    funext c
    simp [mul_assoc]
  refine ⟨e ▸ hF, fun u x => ?_⟩
  refine Eq.trans (congrArg (fun f => (((isExpLieAlgebra K n).rightUAction u f :
    (isExpLieAlgebra K n).smoothFuns (F := ℂ)) : archGroup K n → ℂ) x⁻¹) (Subtype.ext e.symm : _ = (⟨_, hF⟩ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)))) ?_
  rw [hD u x⁻¹, ← integral_mul_left_eq_self (μ := ν) (fun a =>
    ((isExpLieAlgebra K n).rightUAction u ⟨fun g => β₁ g⁻¹, h₁⟩ : archGroup K n → ℂ) a⁻¹ * β₂ (a⁻¹ * x)) x]
  congr 1
  funext c
  simp [mul_assoc]
