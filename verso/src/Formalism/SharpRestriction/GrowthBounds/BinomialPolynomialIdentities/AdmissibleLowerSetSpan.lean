import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SaturatedLowerSetSpanOfLowerSetTypesSpan
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint

namespace Formalism.MainNotions.G.ColumnFamilies

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem admissible_lowerSet_span (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.SaturatedLowerSetSpan D := saturatedLowerSetSpan_of_lowerSetTypesSpan D (lower_set_types_span D)

end Formalism.MainNotions.G.ColumnFamilies
