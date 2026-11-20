import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthZeta

namespace PI.EF

/- English proof (translation)
Establish `h` using `lGrowth_of hB (zetaGrowth_of hZ)`. Establish `hm : max (300000 : ℝ) 53946 = 300000` using `by norm_num`. Rewrite `h` using `[hm]`. Then use the resulting hypothesis.
-/
theorem lGrowth_of_right (hB : PI.LBoundRight) (hZ : PI.ZetaBoundRight) : LGrowth 7 300000 := by
  have h := lGrowth_of hB (zetaGrowth_of hZ)
  have hm : max (300000 : ℝ) 53946 = 300000 := by norm_num
  rwa [hm] at h

end PI.EF
