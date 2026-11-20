import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.CasimirRealScalar
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.CommutatorAdjointHolds

namespace CompanionTheory.D.gk.HC

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kFiniteWordBound_indefUnitary : WordBd := wordBd_of casimirActsByScalar_indefUnitary

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kFiniteVectors_analytic_indefiniteUnitary : GlobalTheory.Published.KFiniteAnalyticUJ := kFiniteAnalytic_of K_finite_smooth_vectors kFiniteWordBound_indefUnitary

end CompanionTheory.D.gk.HC
