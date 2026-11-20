import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.AutomorphicFormsLeSm
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay

open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.Esk.HyperbolicKernelContinuity

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem norm_omega {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Ideles F) : ‖((ω.1 z : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  have e3 : ω.1 z ^ n = 1 := by
    have := DFunLike.congr_fun e2 z
    simpa using this
  have e4 : ((ω.1 z : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, e3, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one e4 hn.ne'

end UpperTheory.Esk.HyperbolicKernelContinuity

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Esk.hyperbolic_kernel_continuity : UpperTheory.Esk.H1c := by
  intro F _ _ _ k c ω φ hω hφ hcusp
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_cuspForms ((UpperTheory.V.Fb.isCuspForm_iff φ).1 hcusp)
  refine ⟨C, fun g => ?_⟩
  obtain ⟨s, y, hy, rfl⟩ := exists_centralSection_mul_mem_normOneGL g
  have hz : centralSection F 2 s = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (posIdeleHom F (rpowHom ((2 * Module.finrank ℚ F : ℝ))⁻¹ s)) := by
    refine Units.ext ?_
    ext i j
    simp [centralSection, scalarUnits_apply, coe_diagUnits, Matrix.diagonal_apply, Matrix.scalar_apply]
  rw [hz, hφ.cent, norm_mul, UpperTheory.Esk.HyperbolicKernelContinuity.norm_omega hω, one_mul]
  exact hC y hy
