import ReciprocityTheory.SemistableReduction.SemiDeg
import ReciprocityTheory.SemistableReduction.SemiContract
import ReciprocityTheory.SemistableReduction.LatAll

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem semiPoint : SemiPointStatement := semiDeg_holds degAdd

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem semistable : SemistableStatement := semiContract_holds semiPoint degAdd

end ReciprocityTheory.MultiplicativeHeights.Closed
