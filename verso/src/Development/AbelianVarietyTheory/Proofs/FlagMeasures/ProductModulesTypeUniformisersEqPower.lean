import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VENatEqZero

namespace GlobalTheory.HTThetaLeaf

/- English proof (translation)
Unfold `Formalism.L2.SG.NGHTie.HTTheta`. Conclude with `GlobalTheory.TypeUnifProd.main`.
-/
theorem main : Formalism.L2.SG.NGHTie.HTTheta := by
  unfold Formalism.L2.SG.NGHTie.HTTheta
  exact GlobalTheory.TypeUnifProd.main

end GlobalTheory.HTThetaLeaf
