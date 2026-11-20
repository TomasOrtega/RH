import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNBoxOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PjFrameRow

namespace Formalism.L2.SG.Pf.NcReal.JX

/- English proof (translation)
The claim follows from `refNBox_of FR.frameRow_holds`.
-/
theorem refNBox_holds : RefNBox := refNBox_of FR.frameRow_holds

end Formalism.L2.SG.Pf.NcReal.JX
