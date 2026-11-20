import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.FwdEx
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.BwdEx
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AssembleG

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepPairG_holds : StepPairG := stepPairG_of_fwd_bwd fwdEx bwdEx

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem algAll_holds : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.AlgAll := algAll_of stepPairG_holds

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
