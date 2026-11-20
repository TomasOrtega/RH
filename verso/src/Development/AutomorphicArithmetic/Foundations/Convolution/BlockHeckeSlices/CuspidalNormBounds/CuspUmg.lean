import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

/- English proof (translation)
Introduce `E _ _ _ n f hf`. Use `⟨⟨hf.1.isLeftInvariant, level_of hf.1.isSmooth hf.1.isKFinite, ?_⟩, hf.2⟩` and prove the remaining obligations. Take `⟨C₀, N, hC₀⟩` from `hf.1.hasModerateGrowth`. Use `⟨N, fun u => ?_⟩` and prove the remaining obligations. Use `show HasGrowth (uC E n u f).1 N`.

Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, fun g => by simp⟩`. Consider the case `tmul c x`. Take `⟨C, hC⟩` from `hasGrowth_uAction x hf.1.isSmoothKZ ⟨C₀, hC₀⟩`. Use `⟨‖c‖ * C, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[uC_tmul, mul_assoc]`. Conclude with `(norm_mul c _).le.trans (mul_le_mul_of_nonneg_left (hC g) (norm_nonneg c))`. Consider the case `add x y hx hy`. Rewrite using `[map_add]`. Conclude with `hx.add hy`.
-/
theorem UpperTheory.ConvolutionTheory.BW.cuspUmg :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.CuspUmg E := by
  intro E _ _ _ n f hf
  refine ⟨⟨hf.1.isLeftInvariant, level_of hf.1.isSmooth hf.1.isKFinite, ?_⟩, hf.2⟩
  obtain ⟨C₀, N, hC₀⟩ := hf.1.hasModerateGrowth
  refine ⟨N, fun u => ?_⟩
  show HasGrowth (uC E n u f).1 N
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, fun g => by simp⟩
  | tmul c x =>
    obtain ⟨C, hC⟩ := hasGrowth_uAction x hf.1.isSmoothKZ ⟨C₀, hC₀⟩
    refine ⟨‖c‖ * C, fun g => ?_⟩
    rw [uC_tmul, mul_assoc]
    exact (norm_mul c _).le.trans (mul_le_mul_of_nonneg_left (hC g) (norm_nonneg c))
  | add x y hx hy =>
    rw [map_add]
    exact hx.add hy
