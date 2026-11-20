import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TBNFinal

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

/- English proof (translation)
The claim follows from `thetaBasis_holds`.
-/
theorem lemmaN (_hd : DimStatement) : NStatement := thetaBasis_holds

end ReciprocityTheory.ChartRestriction.G.I2
