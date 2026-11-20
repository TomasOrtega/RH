import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.TrDetPfH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowBlockCovolOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ReImESymmAdd

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

/- English proof (translation)
The claim follows from `TrD.trDetUnimod_of TrD.detHOne_holds`.
-/
theorem trDetUnimod_holds : TrDetUnimod := TrD.trDetUnimod_of TrD.detHOne_holds

/- English proof (translation)
The claim follows from `rowBlockCovol_of trDetUnimod_holds`.
-/
theorem rowBlockCovol_holds : RowBlockCovol := rowBlockCovol_of trDetUnimod_holds

/- English proof (translation)
The claim follows from `blockCovol_of rowBlockCovol_holds`.
-/
theorem blockCovol_holds : BlockCovol := blockCovol_of rowBlockCovol_holds

end Formalism.L2.SG.Pf.NcReal.JX.CovB
