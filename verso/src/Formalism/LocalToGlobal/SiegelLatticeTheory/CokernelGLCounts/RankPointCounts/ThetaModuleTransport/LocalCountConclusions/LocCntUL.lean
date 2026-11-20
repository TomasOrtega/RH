import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.PartialA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.AlgAllHolds

namespace Formalism.L2.SG.LocalCountModules

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem localCountUnitLocal_holds : Formalism.L2.SG.LocalCountModules.LocCntUL.LocCntUL :=
  Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL.locCntUL_of_alg Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic.algAll_holds

end Formalism.L2.SG.LocalCountModules
