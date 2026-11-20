import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.DualLowestKTypeOfStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.K2V

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem k2Vd (n : ℕ) : EigenspaceWeightConeDual n :=
  TwistedDualLemmas.dualLowestKType_of_standard (k2V n)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
