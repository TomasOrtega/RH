import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitG

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

/- English proof (translation)
Introduce `E _ _ _ X DF P`. Distinguish the cases in `h : X.la1 < P.th`. Conclude with `split_pos X P h`. Conclude with `⟨⊥, split_bot X P h⟩`.
-/
theorem split (hx : Ext.All) : SplitStatement := by
  intro E _ _ _ X DF P
  by_cases h : X.la1 < P.th
  · exact split_pos X P h
  · exact ⟨⊥, split_bot X P h⟩

end ReciprocityTheory.ChartRestriction.G.I2
