import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorStatus
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgStatus
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CmAllOf

namespace Formalism.L2.Th1.CM

/- English proof (translation)
The claim follows from `ReciprocityTheory.ChartRestriction.L1.cm1`.
-/
theorem cm1 : JInvariantIntegrality := ReciprocityTheory.ChartRestriction.L1.cm1
/- English proof (translation)
The claim follows from `ReciprocityTheory.ChartRestriction.L1.cm4`.
-/
theorem cm4 : CM4 := ReciprocityTheory.ChartRestriction.L1.cm4
/- English proof (translation)
The claim follows from `ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree`.
-/
theorem cm3 : CM3 := ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree
/- English proof (translation)
The claim follows from `h.out`.
-/
theorem cm2 [h : Fact CM2] : CM2 := h.out

end Formalism.L2.Th1.CM
