import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Proceed by induction.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
