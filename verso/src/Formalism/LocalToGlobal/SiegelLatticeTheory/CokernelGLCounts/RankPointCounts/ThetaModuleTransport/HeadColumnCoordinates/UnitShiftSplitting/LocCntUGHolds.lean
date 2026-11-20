import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AlgGUT
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScaleFinal

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem algGUT_holds : AlgGUT := by
  intro F _ _ _ E _ _ _ _ M g hg r T T' hT hq Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ _ _ hrel hG₁ hG₂ hT0
  exact Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.algGAllT_holds F E M g hg r T T' hT hq Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ hrel hG₁ hG₂ hT0

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locCntUG_holds : Formalism.L2.SG.LocalCountModules.LocCntUG.LocCntUG := locCntUG_of_algGUT algGUT_holds

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
