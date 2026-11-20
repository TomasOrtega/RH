import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StandardKTypeOfCentralChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CentralChar

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
The claim follows from `standardKType_of_centralChar n (centralChar n)`.
-/
theorem k1V (n : ℕ) : LowestKTypeEulerTensorStandard n :=
  standardKType_of_centralChar n (centralChar n)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
