import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.CasimirRealScalar
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.CommutatorAdjointHolds

namespace CompanionTheory.D.gk.HC

/- English proof (translation)
The claim follows from `wordBd_of casimirActsByScalar_indefUnitary`.
-/
theorem kFiniteWordBound_indefUnitary : WordBd := wordBd_of casimirActsByScalar_indefUnitary

/- English proof (translation)
The claim follows from `kFiniteAnalytic_of K_finite_smooth_vectors kFiniteWordBound_indefUnitary`.
-/
theorem kFiniteVectors_analytic_indefiniteUnitary : GlobalTheory.Published.KFiniteAnalyticUJ := kFiniteAnalytic_of K_finite_smooth_vectors kFiniteWordBound_indefUnitary

end CompanionTheory.D.gk.HC
