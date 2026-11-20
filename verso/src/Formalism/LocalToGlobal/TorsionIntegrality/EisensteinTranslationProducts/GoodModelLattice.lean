import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HeckeKernelIntegralValue
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HeckeKernelCellContinuous
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HeckeKernelLineZero
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.EisensteinS2LimitFormulaOfHkLimit
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorEvenTheta
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.AreaCov
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.GoodModelLatticeGen

namespace Formalism.L2.Th1.F

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hkSummable : HkSummable := hecke_kernel_summable
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hkRowIntegral : HkRowIntegral := hecke_kernel_line_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hkCellBound : HkCellBound := hecke_kernel_cell_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hkCellCont : HkCellCont := hecke_kernel_cell_continuous
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hkIntZero : HkIntZero := hecke_kernel_integral_zero
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hkIntValue : HkIntValue := hecke_kernel_integral_value
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hkJRules : HkJRules := hecke_kernel_j_rules
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hkRowZero : HkRowZero := hecke_kernel_line_zero
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hkIntLimit : HkIntLimit := hkIntLimit_of hecke_kernel_integral_value hecke_kernel_j_rules
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hkLimit : HkLimit :=
  hkLimit_of hecke_kernel_summable hecke_kernel_line_integral hecke_kernel_cell_bound hecke_kernel_cell_continuous hecke_kernel_integral_zero
    hecke_kernel_line_zero (hkIntLimit_of hecke_kernel_integral_value hecke_kernel_j_rules)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eisenstein_s2_limit_formula : EisensteinS2LimitFormula := eisensteinS2LimitFormula_of_hkLimit hkLimit
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorTh0 : TaylorTh0 := taylor_even_theta
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem areaCovolume : AreaCovolume := area_covolume
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uSerLattice : USerLattice := u_series_lattice
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem goodModelLattice : GoodModelLattice := good_model_lattice

end Formalism.L2.Th1.F
