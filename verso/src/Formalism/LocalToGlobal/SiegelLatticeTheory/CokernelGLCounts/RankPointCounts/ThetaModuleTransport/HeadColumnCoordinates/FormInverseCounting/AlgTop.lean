import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AlgInj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.ProjPSurjective
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.ThetaPMem

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locCnt0L_of_stepPair (h : StepPair) : Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of_pair h stepInj Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear.stepAdj

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
