import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodModKLocalGen

namespace GlobalTheory.DiffModProd

/- English proof (translation)
Unfold `Formalism.L2.SG.NGHTie.HTDelta`. Conclude with `finprod_modK_localGen`.
-/
theorem htDelta : Formalism.L2.SG.NGHTie.HTDelta := by
  unfold Formalism.L2.SG.NGHTie.HTDelta
  exact finprod_modK_localGen

end GlobalTheory.DiffModProd
