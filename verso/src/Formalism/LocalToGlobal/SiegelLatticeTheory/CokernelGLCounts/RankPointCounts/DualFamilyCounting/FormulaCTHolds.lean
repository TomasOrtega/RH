import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCT
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame

namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
/- English proof (translation)
The claim follows from `formulaCT_of DualityBasisChange.frameBasisL_holds`.
-/
theorem formulaCT_holds : FormulaCT := formulaCT_of DualityBasisChange.frameBasisL_holds

end Formalism.L2.SG.Pf.Cnt
