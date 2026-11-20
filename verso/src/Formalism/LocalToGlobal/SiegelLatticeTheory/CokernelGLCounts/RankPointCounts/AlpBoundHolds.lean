import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntegralApproximation
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut

namespace Formalism.L2.SG.IntegralApproximation

/- English proof (translation)
The claim follows from `alpBoundU D`.
-/
theorem AlpBound_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.DataCut.AlpBound D := alpBoundU D

end Formalism.L2.SG.IntegralApproximation
