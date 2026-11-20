import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CharMain

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

/- English proof (translation)
The claim follows from `ChA.char_main hx`.
-/
theorem char (hx : Ext.All) : CharStatement :=
  ChA.char_main hx

end ReciprocityTheory.ChartRestriction.G.I2
