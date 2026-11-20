import ReciprocityTheory.SemistableReduction.SemiDeg
import ReciprocityTheory.SemistableReduction.SemiContract
import ReciprocityTheory.SemistableReduction.LatAll

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

/- English proof (translation)
The claim follows from `semiDeg_holds degAdd`.
-/
theorem semiPoint : SemiPointStatement := semiDeg_holds degAdd

/- English proof (translation)
The claim follows from `semiContract_holds semiPoint degAdd`.
-/
theorem semistable : SemistableStatement := semiContract_holds semiPoint degAdd

end ReciprocityTheory.MultiplicativeHeights.Closed
