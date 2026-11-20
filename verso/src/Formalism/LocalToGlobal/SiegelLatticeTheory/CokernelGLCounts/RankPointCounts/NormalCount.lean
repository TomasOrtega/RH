import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardMulConjEqLeOfFractionalIdeal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalInvariants
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.VanishingOrbitalPoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

namespace Formalism.L2.SG.NGCut.NormalCount

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem NormCountG_holds : Formalism.L2.SG.NGCut.NormalInvariants.NormCountG := by
  intro E _ _ _ J m hJ hm S hS
  exact Formalism.L2.SG.NGCut.TorsionTotientBound.card_mul_conj_eq_le_of_fractionalIdeal E J m hJ hm S hS

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem NormCount_holds : Formalism.L2.SG.NGCut.NormalInvariants.NormCount :=
  Formalism.L2.SG.NGCut.NormalInvariants.normCount_of NormCountG_holds

end Formalism.L2.SG.NGCut.NormalCount
