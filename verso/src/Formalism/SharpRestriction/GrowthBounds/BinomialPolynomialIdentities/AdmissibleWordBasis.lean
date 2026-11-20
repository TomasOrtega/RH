import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ExistsDominantTopWeightNonzero
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.CardPathIndexWeightMemEqMulChoose
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.TorusComponentMemDominatedWeightPolynomials

namespace Formalism.MainNotions.G.ColumnFamilies

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem restOne : RestOne := restOne_of restWord restTop restSplit

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem admissible_word_basis (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.FirstLettersLowerSet D := firstLettersLowerSet_of_restWord_restOne D restWord restOne

end Formalism.MainNotions.G.ColumnFamilies
