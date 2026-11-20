import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitG

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem split (hx : Ext.All) : SplitStatement := by
  intro E _ _ _ X DF P
  by_cases h : X.la1 < P.th
  · exact split_pos X P h
  · exact ⟨⊥, split_bot X P h⟩

end ReciprocityTheory.ChartRestriction.G.I2
