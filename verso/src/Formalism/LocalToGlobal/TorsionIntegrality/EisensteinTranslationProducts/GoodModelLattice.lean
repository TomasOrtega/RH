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
The claim follows from `hecke_kernel_summable`.
-/
theorem hkSummable : HkSummable := hecke_kernel_summable
/- English proof (translation)
The claim follows from `hecke_kernel_line_integral`.
-/
theorem hkRowIntegral : HkRowIntegral := hecke_kernel_line_integral
/- English proof (translation)
The claim follows from `hecke_kernel_cell_bound`.
-/
theorem hkCellBound : HkCellBound := hecke_kernel_cell_bound
/- English proof (translation)
The claim follows from `hecke_kernel_cell_continuous`.
-/
theorem hkCellCont : HkCellCont := hecke_kernel_cell_continuous
/- English proof (translation)
The claim follows from `hecke_kernel_integral_zero`.
-/
theorem hkIntZero : HkIntZero := hecke_kernel_integral_zero
/- English proof (translation)
The claim follows from `hecke_kernel_integral_value`.
-/
theorem hkIntValue : HkIntValue := hecke_kernel_integral_value
/- English proof (translation)
The claim follows from `hecke_kernel_j_rules`.
-/
theorem hkJRules : HkJRules := hecke_kernel_j_rules
/- English proof (translation)
The claim follows from `hecke_kernel_line_zero`.
-/
theorem hkRowZero : HkRowZero := hecke_kernel_line_zero
/- English proof (translation)
The claim follows from `hkIntLimit_of hecke_kernel_integral_value hecke_kernel_j_rules`.
-/
theorem hkIntLimit : HkIntLimit := hkIntLimit_of hecke_kernel_integral_value hecke_kernel_j_rules
/- English proof (translation)
The claim follows from `hkLimit_of hecke_kernel_summable hecke_kernel_line_integral hecke_kernel_cell_bound hecke_kernel_cell_continuous hecke_kernel_integral_zero hecke_kernel_line_zero (hkIntLimit_of hecke_kernel_integral_value hecke_kernel_j_rules)`.
-/
theorem hkLimit : HkLimit :=
  hkLimit_of hecke_kernel_summable hecke_kernel_line_integral hecke_kernel_cell_bound hecke_kernel_cell_continuous hecke_kernel_integral_zero
    hecke_kernel_line_zero (hkIntLimit_of hecke_kernel_integral_value hecke_kernel_j_rules)
/- English proof (translation)
The claim follows from `eisensteinS2LimitFormula_of_hkLimit hkLimit`.
-/
theorem eisenstein_s2_limit_formula : EisensteinS2LimitFormula := eisensteinS2LimitFormula_of_hkLimit hkLimit
/- English proof (translation)
The claim follows from `taylor_even_theta`.
-/
theorem taylorTh0 : TaylorTh0 := taylor_even_theta
/- English proof (translation)
The claim follows from `area_covolume`.
-/
theorem areaCovolume : AreaCovolume := area_covolume
/- English proof (translation)
The claim follows from `u_series_lattice`.
-/
theorem uSerLattice : USerLattice := u_series_lattice
/- English proof (translation)
The claim follows from `good_model_lattice`.
-/
theorem goodModelLattice : GoodModelLattice := good_model_lattice

end Formalism.L2.Th1.F
