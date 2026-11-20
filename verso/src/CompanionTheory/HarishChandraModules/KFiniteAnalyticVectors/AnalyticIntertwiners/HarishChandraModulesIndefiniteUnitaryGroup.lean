import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SymmetricPowerMatrix
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.GrowthOfBasic
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.KSpanFinB
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraThirdIndefiniteUnitary
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.LocalPointData

namespace CompanionTheory.D.gk.HC

/- English proof (translation)
The claim follows from `uIrr_of K_finite_smooth_vectors casimirActsByScalar_indefUnitary`.
-/
theorem uIrr : UIrr := uIrr_of K_finite_smooth_vectors casimirActsByScalar_indefUnitary

/- English proof (translation)
The claim follows from `uAdm_of K_finite_smooth_vectors`.
-/
theorem uAdm : UAdm := uAdm_of K_finite_smooth_vectors

/- English proof (translation)
The claim follows from `clause1_of K_finite_smooth_vectors integral_weights uIrr uAdm`.
-/
theorem clause1 : Clause1 := clause1_of K_finite_smooth_vectors integral_weights uIrr uAdm

/- English proof (translation)
The claim follows from `clause2_of clause1 K_finite_smooth_vectors casimirActsByScalar_indefUnitary harish_chandra_descent`.
-/
theorem clause2 : Clause2 := clause2_of clause1 K_finite_smooth_vectors casimirActsByScalar_indefUnitary harish_chandra_descent

/- English proof (translation)
The claim follows from `hcm_of clause1 clause2 harishChandraThird_indefiniteUnitary kFiniteVectors_analytic_indefiniteUnitary`.
-/
theorem print_harishChandraModules : GlobalTheory.Published.HarishChandraModules :=
  hcm_of clause1 clause2 harishChandraThird_indefiniteUnitary kFiniteVectors_analytic_indefiniteUnitary

end CompanionTheory.D.gk.HC
