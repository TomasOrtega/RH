import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.FwdEx
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.BwdEx
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AssembleG

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

/- English proof (translation)
The claim follows from `stepPairG_of_fwd_bwd fwdEx bwdEx`.
-/
theorem stepPairG_holds : StepPairG := stepPairG_of_fwd_bwd fwdEx bwdEx

/- English proof (translation)
The claim follows from `algAll_of stepPairG_holds`.
-/
theorem algAll_holds : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.AlgAll := algAll_of stepPairG_holds

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
