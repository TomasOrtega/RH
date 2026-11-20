import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional

namespace GlobalTheory.CompanionTheory.KModOfStep

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem kModOf : CompanionTheory.RgExh.Fin.KModOf := by
  intro n ε H _ _ _ σ hU hI
  exact CompanionTheory.D.LK.hKModExists n ε H σ hU hI

end GlobalTheory.CompanionTheory.KModOfStep
